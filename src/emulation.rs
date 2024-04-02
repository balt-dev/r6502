//! Handles everything pertaining to actual emulation of a 6502 processor.

use crate::{AddressMode, Instruction, Opcode, State, Status};

/// A trait dictating a memory read callback for an emulator.
/// If you want to easily create a one-off implementation, see [`FunctionReadCallback`].
pub trait ReadCallback {
    /// The callback to be called when memory is read.
    /// This will be called in place of actually reading the memory!
    fn callback(&mut self, state: &mut State, address: u16) -> u8;
}

/// A trait dictating a memory write callback for an emulator.
/// If you want to easily create a one-off implementation, see [`FunctionWriteCallback`].
pub trait WriteCallback {
    /// The callback to be called when memory is written.
    /// This will be called in place of actually writing the memory!
    fn callback(&mut self, state: &mut State, address: u16, byte: u8);
}

/// A helper for easily creating simple implementations of [`ReadCallback`].
pub struct FunctionReadCallback<F>(pub F);

impl<F> ReadCallback for FunctionReadCallback<F>
where
    F: FnMut(&mut State, u16) -> u8,
{
    fn callback(&mut self, state: &mut State, address: u16) -> u8 {
        self.0(state, address)
    }
}

/// A helper for easily creating simple implementations of [`WriteCallback`].
pub struct FunctionWriteCallback<F>(pub F);

impl<F> WriteCallback for FunctionWriteCallback<F>
where
    F: FnMut(&mut State, u16, u8),
{
    fn callback(&mut self, state: &mut State, address: u16, byte: u8) {
        self.0(state, address, byte);
    }
}

/// Default implementor of [`ReadCallback`] for [`Emulator`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, core::hash::Hash, Ord, PartialOrd)]
pub struct DefaultReadCallback;

impl ReadCallback for DefaultReadCallback {
    fn callback(&mut self, state: &mut State, address: u16) -> u8 {
        state.memory[address as usize]
    }
}

/// Default implementor of [`WriteCallback`] for [`Emulator`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, core::hash::Hash, Ord, PartialOrd)]
pub struct DefaultWriteCallback;

impl WriteCallback for DefaultWriteCallback {
    fn callback(&mut self, state: &mut State, address: u16, byte: u8) {
        state.memory[address as usize] = byte;
    }
}

#[derive(Clone, PartialEq, Eq, core::hash::Hash)]
/// A wrapper around state to aid in emulation.
pub struct Emulator<R: ReadCallback, W: WriteCallback> {
    /// Contains the state of the emulator.
    pub state: State,
    /// Contains a callback to be called on memory reads.
    pub read_callback: R,
    /// Contains a callback to be called on memory writes.
    pub write_callback: W,
}

/// Gets the top and bottom nibbles of a byte
#[inline]
fn to_bcd_nibbles(value: u8) -> (u8, u8) {
    (value >> 4, value & 0xF)
}

/// Makes a byte from nibbles, also returning an overflow value if it was too large
#[inline]
fn from_bcd_nibbles(mut low: u8, mut high: u8) -> (u8, bool) {
    let mut overflow = false;
    high += low / 10;
    low %= 10;
    if high > 9 {
        high %= 10;
        overflow = true;
    }
    ((high << 4) + low, overflow)
}

impl<R: ReadCallback, W: WriteCallback> Emulator<R, W> {
    /// Sets the program counter in a way allowing for call chaining.
    #[inline]
    #[must_use]
    pub const fn with_program_counter(mut self, counter: u16) -> Self {
        self.state.program_counter = counter;
        self
    }

    /// Sets the ROM in a way allowing for call chaining.
    #[inline]
    #[must_use]
    pub const fn with_rom(mut self, rom: [u8; 256 * 256]) -> Self {
        self.state.memory = rom;
        self
    }

    /// Sets the ROM in a way allowing for call chaining.
    ///
    /// This version of the method copies the slice into rom at the given location.
    ///
    /// # Panics
    /// Panics if the rom is too small to hold the slice at the given location.
    #[inline]
    #[must_use]
    pub fn with_rom_from(mut self, slice: &[u8], location: u16) -> Self {
        self.state.memory[location as usize..location as usize + slice.len()]
            .copy_from_slice(slice);
        self
    }

    /// Sets the processor status in a way allowing for call chaining.
    #[inline]
    #[must_use]
    pub const fn with_status(mut self, status: Status) -> Self {
        self.state.status = status;
        self
    }

    /// Gets a reference to a single page of memory.
    #[inline]
    #[must_use]
    pub fn page(&self, page: u8) -> &[u8; 256] {
        // NOTE:
        // This gets optimized down to run without any runtime checks in release mode, but not debug mode.
        // See https://godbolt.org/z/nos8W9nK3 for details.
        (&self.state.memory[(page as usize) * 256..(page as usize + 1) * 256])
            .try_into()
            .unwrap()
    }

    /// Gets a mutable reference to a single page of memory.
    #[inline]
    pub fn page_mut(&mut self, page: u8) -> &mut [u8; 256] {
        (&mut self.state.memory[(page as usize) * 256..(page as usize + 1) * 256])
            .try_into()
            .unwrap()
    }

    /// Read a byte from memory, respecting read callbacks.
    #[must_use]
    #[inline]
    pub fn read(&mut self, index: u16) -> u8 {
        self.read_callback.callback(&mut self.state, index)
    }

    /// Write a byte to memory, respecting write callbacks.
    #[inline]
    pub fn write(&mut self, index: u16, byte: u8) {
        self.write_callback.callback(&mut self.state, index, byte);
    }

    /// Push a byte to the stack.
    pub fn push(&mut self, value: u8) {
        let new_pointer = self.state.stack_pointer.wrapping_sub(1);
        self.write(0x100 + u16::from(self.state.stack_pointer), value);
        self.state.stack_pointer = new_pointer;
    }

    /// Pops a byte from the stack.
    pub fn pop(&mut self) -> u8 {
        self.state.stack_pointer = self.state.stack_pointer.wrapping_add(1);
        self.read(0x100 + u16::from(self.state.stack_pointer))
    }

    /// Gets the byte on the top of the stack.
    #[inline]
    #[must_use]
    pub fn peek(&mut self) -> u8 {
        self.read(0x100 + u16::from(self.state.stack_pointer))
    }

    /// Sets a callback to be called when memory is read from, allowing for memory-mapped reads.
    /// See [`ReadCallback`].
    #[inline]
    #[must_use]
    pub fn with_read_callback<R2: ReadCallback>(self, callback: R2) -> Emulator<R2, W> {
        Emulator {
            state: self.state,
            read_callback: callback,
            write_callback: self.write_callback,
        }
    }

    /// Sets a callback to be called when memory is written to, allowing for memory-mapped writes.
    /// See [`WriteCallback`].
    #[inline]
    #[must_use]
    pub fn with_write_callback<W2: WriteCallback>(self, callback: W2) -> Emulator<R, W2> {
        Emulator {
            state: self.state,
            read_callback: self.read_callback,
            write_callback: callback,
        }
    }
}

impl Default for Emulator<DefaultReadCallback, DefaultWriteCallback> {
    fn default() -> Self {
        Self {
            state: State::default(),
            read_callback: DefaultReadCallback,
            write_callback: DefaultWriteCallback,
        }
    }
}

#[allow(clippy::missing_fields_in_debug)]
impl<R: ReadCallback + core::fmt::Debug, W: WriteCallback + core::fmt::Debug> core::fmt::Debug
    for Emulator<R, W>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("Emulator")
            .field("state", &self.state)
            .field("memory_read_callback", &self.read_callback)
            .field("memory_write_callback", &self.write_callback)
            .finish()
    }
}

#[allow(
    clippy::cast_possible_truncation,
    clippy::enum_glob_use,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss
)]
impl<R: ReadCallback, W: WriteCallback> Emulator<R, W> {
    /// Gets an address from an address mode.
    fn addr(&mut self, mode: AddressMode) -> Option<u16> {
        use AddressMode::*;
        Some(match mode {
            Absolute(addr) => addr,
            ZeroPage(addr) => u16::from(addr),
            Relative(offset) => self
                .state
                .program_counter
                .wrapping_add_signed(i16::from(offset)),
            AbsoluteIndirect(addr) => {
                let high = self.read(addr);
                let low = self.read(addr.wrapping_add(1));
                u16::from_le_bytes([high, low])
            }
            AbsoluteX(addr) => addr.wrapping_add(u16::from(self.state.x_register)),
            AbsoluteY(addr) => addr.wrapping_add(u16::from(self.state.y_register)),
            // Wrapping around the zero page seems to be consistent with actual behavior of the 6502.
            ZeroPageX(addr) => u16::from(addr.wrapping_add(self.state.x_register)),
            ZeroPageY(addr) => u16::from(addr.wrapping_add(self.state.y_register)),
            ZeroPageIndirectX(addr) => {
                let shifted_addr = addr.wrapping_add(self.state.x_register);
                let high = self.read(u16::from(shifted_addr));
                let low = self.read(u16::from(shifted_addr.wrapping_add(1)));
                u16::from_le_bytes([high, low])
            }
            ZeroPageYIndirect(addr) => {
                let high = self.read(u16::from(addr));
                let low = self.read(u16::from(addr.wrapping_add(1)));
                u16::from_le_bytes([high, low]).wrapping_add(u16::from(self.state.y_register))
            }
            _ => return None,
        })
    }

    /// Gets a byte from an address mode
    fn byte(&mut self, mode: AddressMode) -> u8 {
        use AddressMode::*;
        match mode {
            Accumulator => self.state.accumulator,
            Immediate(value) => value,
            _ => {
                let addr = self.addr(mode).expect("address should be valid here");
                self.read(addr)
            }
        }
    }

    /// Writes to the target for an address mode
    fn write_mode(&mut self, mode: AddressMode, value: u8) {
        use AddressMode::*;
        match mode {
            Accumulator => self.state.accumulator = value,
            Immediate(_) => {}
            _ => {
                let addr = self.addr(mode).expect("address should be valid here");
                self.write(addr, value);
            }
        }
    }

    /// Set flags from an arithmetic evaluation
    fn set_flags(&mut self, value: u8) -> u8 {
        self.state.status.set(Status::ZERO, value == 0);
        self.state.status.set(Status::NEGATIVE, (value as i8) < 0);
        value
    }

    /// Steps the state by one opcode.
    ///
    /// On success, returns a boolean value on whether an interrupt was raised that cycle.
    ///
    /// If an interrupt is not handled
    /// (i.e. setting the interrupt flag back to 0 and popping the program counter and status)
    /// before execution continues, your 6502 code may misbehave!
    ///
    /// # Errors
    /// Will error if given an invalid opcode, passing back its index in memory.
    pub fn step(&mut self) -> Result<bool, u16> {
        // Get the opcode from memory
        let mut length = 1;
        let starting_byte = self.read(self.state.program_counter);
        let Some(opcode) = Opcode::load(&[starting_byte])
            .or_else(|needed| {
                // This is a really, REALLY hacky way to do this.
                // However, it doesn't need an allocator.
                length = needed;
                match needed {
                    2 => Opcode::load(&[
                        starting_byte,
                        self.read(self.state.program_counter.wrapping_add(1)),
                    ]),
                    3 => Opcode::load(&[
                        starting_byte,
                        self.read(self.state.program_counter.wrapping_add(1)),
                        self.read(self.state.program_counter.wrapping_add(2)),
                    ]),
                    v => Err(v),
                }
            })
            .expect("all opcodes need between 1 and 3 bytes")
        else {
            // We have an invalid opcode!
            return Err(self.state.program_counter);
        };

        self.process_opcode(opcode, length as u8)
            .ok_or(self.state.program_counter)
    }

    /// Processes a single opcode.
    ///
    /// Returns `None` if the opcode is invalid.
    #[allow(clippy::too_many_lines)]
    pub fn process_opcode(&mut self, opcode: Opcode, opcode_length: u8) -> Option<bool> {
        use Instruction::*;

        let mut increment = true;

        match opcode.instruction {
            LDA => {
                let loaded = opcode.address_mode.map(|v| self.byte(v))?;
                self.state.accumulator = self.set_flags(loaded);
            }
            LDX => {
                let loaded = opcode.address_mode.map(|v| self.byte(v))?;
                self.state.x_register = self.set_flags(loaded);
            }
            LDY => {
                let loaded = opcode.address_mode.map(|v| self.byte(v))?;
                self.state.y_register = self.set_flags(loaded);
            }
            STA => {
                let addr = opcode.address_mode.and_then(|v| self.addr(v))?;
                self.write(addr, self.state.accumulator);
            }
            STX => {
                let addr = opcode.address_mode.and_then(|v| self.addr(v))?;
                self.write(addr, self.state.x_register);
            }
            STY => {
                let addr = opcode.address_mode.and_then(|v| self.addr(v))?;
                self.write(addr, self.state.y_register);
            }
            ADC => opcode.address_mode.map(|mode| {
                let rhs = self.byte(mode);
                if cfg!(feature = "bcd") && self.state.status.contains(Status::DECIMAL) {
                    let lhs = self.state.accumulator;

                    let (high_lhs, low_lhs) = to_bcd_nibbles(lhs);
                    let (high_rhs, low_rhs) = to_bcd_nibbles(rhs);
                    let low_sum =
                        low_lhs + low_rhs + u8::from(self.state.status.contains(Status::CARRY));
                    let (low_carry, low) = (low_sum / 10, low_sum % 10);
                    let high_sum = high_lhs + high_rhs + low_carry;
                    let (sum, carry) = from_bcd_nibbles(low, high_sum);
                    self.state.status.set(Status::CARRY, carry);
                    let overflow_sum = u16::from(from_bcd(lhs))
                        + u16::from(from_bcd(rhs))
                        + u16::from(self.state.status.contains(Status::CARRY));
                    self.state.status.set(
                        Status::OVERFLOW,
                        (lhs & 0x80) != (overflow_sum & 0x80) as u8,
                    );
                    self.state.status.set(Status::ZERO, sum == 0);
                    self.state.status.set(Status::NEGATIVE, (sum as i8) < 0);
                    self.state.accumulator = sum;
                } else {
                    self.state.accumulator = self.adc(rhs);
                }
            })?,
            SBC => opcode.address_mode.map(|mode| {
                let rhs = self.byte(mode);
                if cfg!(feature = "bcd") && self.state.status.contains(Status::DECIMAL) {
                    let lhs = self.state.accumulator;

                    let (high_lhs, low_lhs) = to_bcd_nibbles(lhs);
                    let (high_rhs, low_rhs) = to_bcd_nibbles(rhs);
                    let mut low = low_lhs as i8
                        - low_rhs as i8
                        - i8::from(!self.state.status.contains(Status::CARRY));
                    let mut low_borrow = 0;
                    if low < 0 {
                        low += 10;
                        low_borrow = 1;
                    }
                    let mut high = high_lhs as i8 - high_rhs as i8 - low_borrow;
                    self.state.status.set(Status::OVERFLOW, false);
                    if high < 0 {
                        high += 10;
                        self.state.status.set(Status::CARRY, false); // Take the carry out
                        if !self.state.status.contains(Status::CARRY) {
                            self.state.status.set(Status::OVERFLOW, true);
                        }
                    } else {
                        self.state.status.set(Status::CARRY, true);
                    }
                    let (diff, _) = from_bcd_nibbles(low as u8, high as u8);

                    self.state.status.set(Status::NEGATIVE, (diff as i8) < 0);
                    self.state.status.set(Status::ZERO, diff == 0);
                    self.state.accumulator = diff;
                } else {
                    self.state.accumulator = self.adc(!rhs);
                }
            })?,
            INC => opcode.address_mode.map(|mode| {
                let new = self.byte(mode).wrapping_add(1);
                self.set_flags(new);
                self.write_mode(mode, new);
            })?,
            INX => self.state.x_register = self.set_flags(self.state.x_register.wrapping_add(1)),
            INY => self.state.y_register = self.set_flags(self.state.y_register.wrapping_add(1)),
            DEC => opcode.address_mode.map(|mode| {
                let new = self.byte(mode).wrapping_sub(1);
                self.set_flags(new);
                self.write_mode(mode, new);
            })?,
            DEX => self.state.x_register = self.set_flags(self.state.x_register.wrapping_sub(1)),
            DEY => self.state.y_register = self.set_flags(self.state.y_register.wrapping_sub(1)),
            ASL => opcode.address_mode.map(|mode| {
                let mut old = self.byte(mode);
                self.state.status.set(Status::CARRY, old & 0b1000_0000 != 0);
                old <<= 1;
                self.set_flags(old);
                self.write_mode(mode, old);
            })?,
            LSR => opcode.address_mode.map(|mode| {
                let mut old = self.byte(mode);
                self.state.status.set(Status::CARRY, old & 0b0000_0001 != 0);
                old >>= 1;
                self.set_flags(old);
                self.write_mode(mode, old);
            })?,
            ROL => opcode.address_mode.map(|mode| {
                let mut old = self.byte(mode);
                let high_bit = (old & 0b1000_0000) != 0;
                old <<= 1;
                old |= u8::from(self.state.status.contains(Status::CARRY));
                self.state.status.set(Status::CARRY, high_bit);
                self.set_flags(old);
                self.write_mode(mode, old);
            })?,
            ROR => opcode.address_mode.map(|mode| {
                let mut old = self.byte(mode);
                let low_bit = (old & 0b0000_0001) != 0;
                old >>= 1;
                old |= u8::from(self.state.status.contains(Status::CARRY)) << 7;
                self.state.status.set(Status::CARRY, low_bit);
                self.set_flags(old);
                self.write_mode(mode, old);
            })?,
            AND => opcode.address_mode.map(|mode| {
                self.state.accumulator &= self.byte(mode);
                self.set_flags(self.state.accumulator);
            })?,
            ORA => opcode.address_mode.map(|mode| {
                self.state.accumulator |= self.byte(mode);
                self.set_flags(self.state.accumulator);
            })?,
            EOR => opcode.address_mode.map(|mode| {
                self.state.accumulator ^= self.byte(mode);
                self.set_flags(self.state.accumulator);
            })?,
            BIT => opcode.address_mode.map(|mode| {
                let byte = self.byte(mode);
                let result = self.state.accumulator & byte;
                self.state.status.set(Status::ZERO, result == 0);
                self.state
                    .status
                    .set(Status::NEGATIVE, byte & 0b1000_0000 != 0);
                self.state
                    .status
                    .set(Status::OVERFLOW, byte & 0b0100_0000 != 0);
            })?,
            CMP => opcode
                .address_mode
                .map(|mode| self.compare(self.state.accumulator, mode))?,
            CPX => opcode
                .address_mode
                .map(|mode| self.compare(self.state.x_register, mode))?,
            CPY => opcode
                .address_mode
                .map(|mode| self.compare(self.state.y_register, mode))?,
            inst @ (BCC | BNE | BPL | BVC | BCS | BEQ | BMI | BVS) => {
                opcode.address_mode.and_then(|mode| {
                    let mask = match inst {
                        BCC | BCS => Status::CARRY,
                        BNE | BEQ => Status::ZERO,
                        BPL | BMI => Status::NEGATIVE,
                        BVC | BVS => Status::OVERFLOW,
                        _ => unreachable!(),
                    };
                    let inverse = matches!(inst, BCC | BNE | BPL | BVC);
                    if inverse ^ self.state.status.contains(mask) {
                        self.state.program_counter = self.addr(mode)?;
                    }
                    Some(())
                })?;
            }
            TAX => self.state.x_register = self.set_flags(self.state.accumulator),
            TAY => self.state.y_register = self.set_flags(self.state.accumulator),
            TXA => self.state.accumulator = self.set_flags(self.state.x_register),
            TYA => self.state.accumulator = self.set_flags(self.state.y_register),
            TSX => self.state.x_register = self.set_flags(self.state.stack_pointer),
            TXS => self.state.stack_pointer = self.state.x_register,
            PHA => self.push(self.state.accumulator),
            PLA => {
                let new_acc = self.pop();
                self.state.accumulator = self.set_flags(new_acc);
            }
            PHP => self.push((self.state.status | Status::UNUSED | Status::BREAK).bits()),
            PLP => self.state.status = Status::from_bits_retain(self.pop()) | Status::UNUSED,
            JMP => opcode.address_mode.and_then(|mode| {
                self.state.program_counter = self.addr(mode)?;
                increment = false;
                Some(())
            })?,
            JSR => opcode.address_mode.and_then(|mode| {
                let [high, low] = self
                    .state
                    .program_counter
                    .wrapping_add(u16::from(opcode_length))
                    .wrapping_sub(1)
                    .to_le_bytes();
                self.state.program_counter = self.addr(mode)?;
                self.push(low);
                self.push(high);
                increment = false;
                Some(())
            })?,
            RTS => {
                let addr = u16::from_le_bytes([self.pop(), self.pop()]);
                self.state.program_counter = addr;
            }
            inst @ (CLC | SEC | CLD | SED | CLI | SEI | CLV) => {
                let mask = match inst {
                    CLC | SEC => Status::CARRY,
                    CLD | SED => Status::DECIMAL,
                    CLI | SEI => Status::INTERRUPT_DISABLE,
                    CLV => Status::OVERFLOW,
                    _ => unreachable!(),
                };
                let target = matches!(inst, SEC | SED | SEI);
                self.state.status.set(mask, target);
            }
            BRK => {
                self.force_interrupt();
                return Some(true);
            }
            RTI => {
                self.state.status = Status::from_bits_retain(self.pop()) & !Status::BREAK;
                let bytes = [self.pop(), self.pop()];
                self.state.program_counter = u16::from_le_bytes(bytes);
                increment = false;
            }
            NOP => {}
        }

        if increment {
            self.state.program_counter = self
                .state
                .program_counter
                .wrapping_add(u16::from(opcode_length));
        }

        Some(false)
    }

    /// Requests a maskable interrupt. Returns whether the interrupt happened.
    pub fn request_interrupt(&mut self) -> bool {
        if !self.state.status.contains(Status::INTERRUPT_DISABLE) {
            self.force_interrupt();
            return true;
        }
        false
    }

    /// Forces a non-maskable interrupt.
    pub fn force_interrupt(&mut self) {
        self.state.program_counter = self.state.program_counter.wrapping_add(2);
        let [high, low] = self.state.program_counter.to_le_bytes();
        self.push(low);
        self.push(high);
        self.push((self.state.status | Status::BREAK).bits());
        self.state.status.set(Status::INTERRUPT_DISABLE, true);
    }

    /// Drives CMP, CPX, and CPY
    fn compare(&mut self, lhs: u8, mode: AddressMode) {
        let rhs = self.byte(mode);
        let diff = lhs.wrapping_sub(rhs);

        self.state.status.set(Status::ZERO, diff == 0);
        self.state.status.set(Status::CARRY, (diff as i8) >= 0);
        self.state.status.set(Status::NEGATIVE, (diff as i8) < 0);
    }

    /// Computes binary add with carry
    fn adc(&mut self, rhs: u8) -> u8 {
        let sum = u16::from(self.state.accumulator)
            + u16::from(rhs)
            + u16::from(self.state.status.contains(Status::CARRY));

        let acc = u16::from(self.state.accumulator);
        let rhs = u16::from(rhs);

        self.state.status.set(Status::CARRY, sum > 0xFF);
        self.state
            .status
            .set(Status::OVERFLOW, !(acc ^ rhs) & (acc ^ sum) & 0x80 != 0);

        let sum = sum as u8;

        self.state.status.set(Status::ZERO, sum == 0);
        self.state.status.set(Status::NEGATIVE, (sum as i8) < 0);

        sum
    }
}

/// Converts a value from BCD to a normal number
fn from_bcd(val: u8) -> u8 {
    10 * (val >> 4) + (0x0F & val)
}
