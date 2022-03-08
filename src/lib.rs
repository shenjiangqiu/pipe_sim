use std::{
    collections::VecDeque,
    fmt::{Debug, Display, Error, Formatter},
    marker::PhantomData,
};

pub trait Buffer: Sized {
    type Output;
    type Input;
    type InputInfo;
    type OutputInfo;

    fn output_connect_input<T, F>(self, to: T, f: F) -> ConnectedBufferWithFn<Self, T, F>
    where
        T: Buffer<Input = Self::Output>,
        F: FnMut(Option<&Self::OutputInfo>, Option<&T::InputInfo>) -> u64,
    {
        ConnectedBufferWithFn::new(self, to, f)
    }

    fn input_connect_output<T, F, INFO>(self, from: T, f: F) -> ConnectedBufferWithFn<T, Self, F>
    where
        T: Buffer<Output = Self::Input>,
        F: FnMut(Option<&T::OutputInfo>, Option<&Self::InputInfo>) -> u64,
    {
        ConnectedBufferWithFn::new(from, self, f)
    }
    fn connect_with_fn<T, F>(self, to: T, f: F) -> ConnectedBufferWithFn<Self, T, F>
    where
        T: Buffer<Input = Self::Output>,
        F: FnMut(Option<&Self::OutputInfo>, Option<&T::InputInfo>) -> u64,
    {
        ConnectedBufferWithFn::new(self, to, f)
    }

    fn connect<T>(self, to: T) -> ConnectedBuffer<Self, T>
    where
        T: Buffer<Input = Self::Output>,
    {
        ConnectedBuffer::new(self, to)
    }

    fn cycle(&mut self) {}
    fn input_avaliable(&self) -> bool;
    fn output_avaliable(&self) -> bool;
    fn pop_output(&mut self) -> Option<Self::Output>;
    fn get_output(&self) -> Option<&Self::Output>;
    fn push_input(&mut self, input: Self::Input);

    // to info to calculate the transfer delay
    fn get_input_info(&self) -> Option<&Self::InputInfo>;
    fn get_output_info(&self) -> Option<&Self::OutputInfo>;
}

#[derive(Debug)]
enum ConnectedBufferState {
    Idle,
    WaitingToMove(u64),
}
use ConnectedBufferState::*;

#[derive(Debug)]
pub struct ConnectedBufferWithFn<T, U, F>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
    F: FnMut(Option<&T::OutputInfo>, Option<&U::InputInfo>) -> u64,
{
    pub from: T,
    pub to: U,
    f: F,
    state: ConnectedBufferState,
}

impl<T, U, F> ConnectedBufferWithFn<T, U, F>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
    F: FnMut(Option<&T::OutputInfo>, Option<&U::InputInfo>) -> u64,
{
    /// Description:
    ///    Creates a new ConnectedBuffer
    /// Parameters:
    /// - `from`: The buffer to read from
    /// - `to`: The buffer to write to
    /// - `f`: The function to call when input buffer is ready to be read and the output buffer is ready to be written, F return the cycles to finish the transfer
    pub fn new(from: T, to: U, f: F) -> Self {
        ConnectedBufferWithFn {
            from,
            to,
            f,
            state: Idle,
        }
    }
}

impl<T, U, F> Buffer for ConnectedBufferWithFn<T, U, F>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
    F: FnMut(Option<&T::OutputInfo>, Option<&U::InputInfo>) -> u64,
{
    type Output = U::Output;
    type Input = T::Input;
    type InputInfo = T::InputInfo;

    type OutputInfo = U::OutputInfo;

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
                if let (Some(_x), true) = (self.from.get_output(), self.to.input_avaliable()) {
                    let cycles = (self.f)(self.from.get_output_info(), self.to.get_input_info());
                    self.state = WaitingToMove(if cycles == 0 { 0 } else { cycles - 1 });
                }
            }
            WaitingToMove(cycles) => {
                if cycles == 0 {
                    self.state = Idle;
                    self.to.push_input(self.from.pop_output().unwrap());
                    // if become idle, can immediately calculate the next cycle
                    if let (Some(_), true) = (self.from.get_output(), self.to.input_avaliable()) {
                        let cycles =
                            (self.f)(self.from.get_output_info(), self.to.get_input_info());
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

    fn get_input_info(&self) -> Option<&Self::InputInfo> {
        self.from.get_input_info()
    }

    fn get_output_info(&self) -> Option<&Self::OutputInfo> {
        self.to.get_output_info()
    }
}

#[derive(Debug)]
pub struct ConnectedBuffer<T, U>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
{
    pub from: T,
    pub to: U,
}

impl<T, U> ConnectedBuffer<T, U>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
{
    /// Description:
    ///    Creates a new ConnectedBuffer
    /// Parameters:
    /// - `from`: The buffer to read from
    /// - `to`: The buffer to write to
    /// - `f`: The function to call when input buffer is ready to be read and the output buffer is ready to be written return the cycles to finish the transfer
    pub fn new(from: T, to: U) -> Self {
        ConnectedBuffer { from, to }
    }
}

impl<T, U> Buffer for ConnectedBuffer<T, U>
where
    T: Buffer,
    U: Buffer<Input = T::Output>,
{
    type Output = U::Output;
    type Input = T::Input;
    type InputInfo = T::InputInfo;

    type OutputInfo = U::OutputInfo;

    fn input_avaliable(&self) -> bool {
        self.from.input_avaliable()
    }
    fn output_avaliable(&self) -> bool {
        self.to.output_avaliable()
    }

    fn cycle(&mut self) {
        self.from.cycle();
        // transfer
        if let (Some(_x), true) = (self.from.get_output(), self.to.input_avaliable()) {
            self.to.push_input(self.from.pop_output().unwrap());
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

    fn get_input_info(&self) -> Option<&Self::InputInfo> {
        self.from.get_input_info()
    }

    fn get_output_info(&self) -> Option<&Self::OutputInfo> {
        self.to.get_output_info()
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
    type InputInfo = T;
    type OutputInfo = T;

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

    fn get_input_info(&self) -> Option<&Self::InputInfo> {
        None
    }

    fn get_output_info(&self) -> Option<&Self::OutputInfo> {
        self.buffer.front()
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
    type InputInfo = I;

    type OutputInfo = O;

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

    fn get_input_info(&self) -> Option<&Self::InputInfo> {
        None
    }

    fn get_output_info(&self) -> Option<&Self::OutputInfo> {
        self.get_output()
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

impl<T, U, F> Display for ConnectedBufferWithFn<T, U, F>
where
    T: Buffer + Display,
    U: Buffer<Input = T::Output> + Display,
    F: FnMut(Option<&T::OutputInfo>, Option<&U::InputInfo>) -> u64,
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
        let mut system = buffer.output_connect_input(agg_buffer, |_x, _y| 1);
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
