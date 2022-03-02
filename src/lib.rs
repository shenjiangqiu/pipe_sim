use std::{
    collections::VecDeque,
    fmt::{Debug, Display, Error, Formatter},
    marker::PhantomData,
};

pub trait Buffer: Sized {
    type Output;
    type Input;
    fn output_connect_input<T, F>(self, to: T, f: F) -> ConnectedBuffer<Self, T, F>
    where
        T: Buffer<Input = Self::Output>,
        F: Fn(&Self::Output) -> u64,
    {
        ConnectedBuffer::new(self, to, f)
    }

    fn input_connect_output<T, F>(self, from: T, f: F) -> ConnectedBuffer<T, Self, F>
    where
        T: Buffer<Output = Self::Input>,
        F: Fn(&T::Output) -> u64,
    {
        ConnectedBuffer::new(from, self, f)
    }

    fn cycle(&mut self) {}
    fn input_avaliable(&self) -> bool;
    fn output_avaliable(&self) -> bool;
    fn pop_output(&mut self) -> Option<Self::Output>;
    fn get_output(&self) -> Option<&Self::Output>;
    fn push_input(&mut self, input: Self::Input);
}
#[derive(Debug)]
enum ConnectedBufferState {
    Idle,
    WaitingToMove(u64),
}
use ConnectedBufferState::*;

#[derive(Debug)]
pub struct ConnectedBuffer<T, U, F>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
    F: Fn(&T::Output) -> u64,
{
    pub from: T,
    pub to: U,
    f: F,
    state: ConnectedBufferState,
}

impl<T, U, F> ConnectedBuffer<T, U, F>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
    F: Fn(&T::Output) -> u64,
{
    /// Description:
    ///    Creates a new ConnectedBuffer
    /// Parameters:
    /// - `from`: The buffer to read from
    /// - `to`: The buffer to write to
    /// - `f`: The function to call when input buffer is ready to be read and the output buffer is ready to be written, F return the cycles to finish the transfer
    pub fn new(from: T, to: U, f: F) -> Self {
        ConnectedBuffer {
            from,
            to,
            f,
            state: Idle,
        }
    }
}

impl<T, U, F> Buffer for ConnectedBuffer<T, U, F>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
    F: Fn(&T::Output) -> u64,
{
    type Output = U::Output;
    type Input = T::Input;

    fn input_avaliable(&self) -> bool {
        self.from.input_avaliable()
    }
    fn output_avaliable(&self) -> bool {
        self.to.output_avaliable()
    }

    fn cycle(&mut self) {
        self.from.cycle();

        match self.state {
            Idle => {
                if let (Some(x), true) = (self.from.get_output(), self.to.input_avaliable()) {
                    let cycles = (self.f)(x);
                    self.state = WaitingToMove(if cycles == 0 { 0 } else { cycles - 1 });
                }
            }
            WaitingToMove(cycles) => {
                if cycles == 0 {
                    self.state = Idle;
                    self.to.push_input(self.from.pop_output().unwrap());
                    // if become idle, can immediately calculate the next cycle
                    if let (Some(x), true) = (self.from.get_output(), self.to.input_avaliable()) {
                        let cycles = (self.f)(x);
                        self.state = WaitingToMove(if cycles == 0 { 0 } else { cycles - 1 });
                    }
                } else {
                    self.state = WaitingToMove(cycles - 1);
                }
            }
        }
        self.to.cycle();
    }

    fn pop_output(&mut self) -> Option<Self::Output> {
        self.to.pop_output()
    }

    fn push_input(&mut self, input: Self::Input) {
        self.from.push_input(input);
    }
    fn get_output(&self) -> Option<&Self::Output> {
        self.to.get_output()
    }
}

pub struct DoubleBuffer<T> {
    buffer: VecDeque<T>,
}

impl<T> DoubleBuffer<T> {
    pub fn new() -> Self {
        DoubleBuffer {
            buffer: VecDeque::with_capacity(2),
        }
    }
}

impl<T> Default for DoubleBuffer<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Buffer for DoubleBuffer<T> {
    type Input = T;
    type Output = T;

    fn input_avaliable(&self) -> bool {
        self.buffer.len() < 2
    }

    fn output_avaliable(&self) -> bool {
        !self.buffer.is_empty()
    }

    fn pop_output(&mut self) -> Option<Self::Output> {
        self.buffer.pop_front()
    }

    fn get_output(&self) -> Option<&Self::Output> {
        self.buffer.front()
    }

    fn push_input(&mut self, input: Self::Input) {
        self.buffer.push_back(input);
    }
}

pub struct AggBuffer<I, O, F, Fu, Fr>
where
    F: Fn(I) -> O,
    Fu: Fn(&mut O, &O),
    Fr: Fn(&O) -> bool,
{
    temp_buffer: Option<O>,
    phantom: PhantomData<I>,
    buffer: VecDeque<O>,

    f: F,
    f_u: Fu,
    f_r: Fr,
}

impl<I, O, F, Fu, Fr> AggBuffer<I, O, F, Fu, Fr>
where
    F: Fn(I) -> O,
    Fu: Fn(&mut O, &O),
    Fr: Fn(&O) -> bool,
{
    pub fn new(f: F, f_u: Fu, f_r: Fr) -> Self {
        AggBuffer {
            temp_buffer: None,
            buffer: VecDeque::with_capacity(1),
            f,
            f_r,
            f_u,
            phantom: PhantomData,
        }
    }
}

impl<I, O, F, Fu, Fr> Buffer for AggBuffer<I, O, F, Fu, Fr>
where
    F: Fn(I) -> O,
    Fu: Fn(&mut O, &O),
    Fr: Fn(&O) -> bool,
{
    type Output = O;

    type Input = I;

    fn input_avaliable(&self) -> bool {
        match &self.temp_buffer {
            Some(x) => !(self.f_r)(x),
            None => true,
        }
    }

    fn output_avaliable(&self) -> bool {
        self.buffer.front().is_some()
    }

    fn pop_output(&mut self) -> Option<Self::Output> {
        self.buffer.pop_front()
    }

    fn get_output(&self) -> Option<&Self::Output> {
        self.buffer.front()
    }

    fn push_input(&mut self, input: Self::Input) {
        // first translate
        let temp_out = (self.f)(input);

        // then update the temp buffer
        match self.temp_buffer {
            Some(ref mut x) => {
                (self.f_u)(x, &temp_out);
            }
            None => {
                self.temp_buffer = Some(temp_out);
            }
        }

        if self.buffer.is_empty() && self.temp_buffer.as_ref().map(&self.f_r).unwrap_or(false) {
            self.buffer.push_back(self.temp_buffer.take().unwrap());
        }
    }
}
impl<T> Display for DoubleBuffer<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "DoubleBuffer:{:?}", self.buffer)
    }
}
impl<I, O, F, Fu, Fr> Display for AggBuffer<I, O, F, Fu, Fr>
where
    F: Fn(I) -> O,
    Fu: Fn(&mut O, &O),
    Fr: Fn(&O) -> bool,
    O: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "AggBuffer:{:?},{:?}", self.buffer, self.temp_buffer)
    }
}

impl<T, U, F> Display for ConnectedBuffer<T, U, F>
where
    T: Buffer + Display,
    U: Buffer<Input = T::Output> + Display,
    F: Fn(&T::Output) -> u64,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> {}", self.from, self.to)
    }
}
#[cfg(test)]
mod test {

    use super::*;
    #[test]
    fn test() {
        let buffer: DoubleBuffer<u32> = DoubleBuffer::default();
        let agg_buffer = AggBuffer::new(|x: u32| x as u64, |x, y| *x += *y, |x| *x == 10);
        let mut system = buffer.output_connect_input(agg_buffer, |_x| 1);
        system.push_input(1);
        for i in 0..30 {
            system.cycle();
            println!("{}:{}", i, system);
            if i == 10 {
                assert_eq!(system.get_output(), Some(&10));
                assert!(matches!(system.to.temp_buffer, None))
            }
            if i == 20 {
                assert_eq!(system.get_output(), Some(&10));
                assert!(matches!(system.to.temp_buffer, Some(10)));
                assert_eq!(system.to.buffer.len(), 1);
                assert_eq!(system.from.buffer.len(), 1);
            }
            if i == 21 {
                assert_eq!(system.get_output(), Some(&10));
                assert!(matches!(system.to.temp_buffer, Some(10)));
                assert_eq!(system.to.buffer.len(), 1);
                assert_eq!(system.from.buffer.len(), 2);
            }
            if system.input_avaliable() {
                system.push_input(1);
            }
        }
    }
}
