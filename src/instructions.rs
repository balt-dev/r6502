//! A module containing all structures pertaining to instructions and opcodes.

use core::fmt;
use core::fmt::Formatter;

#[cfg(feature = "arbitrary")]
extern crate std;

/// An enumeration over all 6502 memory addressing modes.
#[derive(Debug, Copy, Clone, PartialEq, Eq, core::hash::Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum AddressMode {
    /// Use the accumulator as the operand.
    Accumulator,
    /// Use the next byte as the operand.
    Immediate(u8),
    /// Use the byte at the address as the operand.
    Absolute(u16),
    /// Use the byte at the address in the zero page as the operand.
    ZeroPage(u8),
    /// Use a byte offset from the current program counter as the operand.
    Relative(i8),
    /// Use a byte at the address stored at the address as the operand.
    AbsoluteIndirect(u16),
    /// Use a byte at the address specified plus the X register as the operand.
    AbsoluteX(u16),
    /// Use a byte at the address specified plus the Y register as the operand.
    AbsoluteY(u16),
    /// Use a byte at the address in the zero page plus the X register as the operand.
    ZeroPageX(u8),
    /// Use a byte at the address in the zero page plus the Y register as the operand.
    ZeroPageY(u8),
    /// Use a byte at the address stored at "the address in the zero page plus the X register" as the operand.
    ZeroPageIndirectX(u8),
    /// Use a byte at the address stored at "the address in the zero page" plus the Y register as the operand.
    ZeroPageYIndirect(u8),
}

impl fmt::Display for AddressMode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AddressMode::Accumulator => Ok(()),
            AddressMode::Immediate(n) => write!(f, "#${n:02X}"),
            AddressMode::Absolute(n) => write!(f, "${n:04X}"),
            AddressMode::ZeroPage(n) => write!(f, "${n:02X}"),
            AddressMode::Relative(n) => write!(f, "${n:02X}"),
            AddressMode::AbsoluteIndirect(n) => write!(f, "(${n:04X})"),
            AddressMode::AbsoluteX(n) => write!(f, "${n:04X},X"),
            AddressMode::AbsoluteY(n) => write!(f, "${n:04X},Y"),
            AddressMode::ZeroPageX(n) => write!(f, "${n:02X},X"),
            AddressMode::ZeroPageY(n) => write!(f, "${n:02X},Y"),
            AddressMode::ZeroPageIndirectX(n) => write!(f, "(${n:02X},X)"),
            AddressMode::ZeroPageYIndirect(n) => write!(f, "(${n:02X}),Y"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, core::hash::Hash)]
#[allow(non_camel_case_types)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
/// An enumeration over all instructions in a 6502.
pub enum Instruction {
    /// Load a byte into the accumulator.
    LDA,
    /// Load a byte into the X register.
    LDX,
    /// Load a byte into the Y register.
    LDY,
    /// Store the accumulator into memory.
    STA,
    /// Store the X register into memory.
    STX,
    /// Store the Y register into memory.
    STY,
    /// Add a byte to the accumulator.
    ADC,
    /// Subtract a byte from the accumulator.
    SBC,
    /// Increment a byte by one.
    INC,
    /// Increment the X register by one.
    INX,
    /// Increment the Y register by one.
    INY,
    /// Decrement a byte by one.
    DEC,
    /// Decrement the X register by one.
    DEX,
    /// Decrement the Y register by one.
    DEY,
    /// Arithmetically bit-shift a byte to the left by one.
    ASL,
    /// Logically bit-shift a byte to the right by one.
    LSR,
    /// Rotate the bits of a byte leftwards, in and out of the carry bit.
    ROL,
    /// Rotate the bits of a byte rightwards, in and out of the carry bit.
    ROR,
    /// Take the bitwise AND of the accumulator and a byte.
    AND,
    /// Take the bitwise OR of the accumulator and a byte.
    ORA,
    /// Take the bitwise XOR of the accumulator and a byte.
    EOR,
    /// Tests a byte's bits with the accumulator.
    BIT,
    /// Compare a byte with the value in the accumulator.
    CMP,
    /// Compare a byte with the value in the X register.
    CPX,
    /// Compare a byte with the value in the Y register.
    CPY,
    /// Branches if the carry bit of the processor status is clear.
    BCC,
    /// Branches if the carry bit of the processor status is set.
    BCS,
    /// Branches if the zero bit of the processor status is clear.
    BNE,
    /// Branches if the zero bit of the processor status is set.
    BEQ,
    /// Branches if the negative bit of the processor status is clear.
    BPL,
    /// Branches if the negative bit of the processor status is set.
    BMI,
    /// Branches if the overflow bit of the processor status is clear.
    BVC,
    /// Branches if the overflow bit of the processor status is set.
    BVS,
    /// Transfers the byte in the accumulator to the X register.
    TAX,
    /// Transfers the byte in the accumulator to the Y register.
    TAY,
    /// Transfers the byte in the X register to the accumulator.
    TXA,
    /// Transfers the byte in the Y register to the accumulator.
    TYA,
    /// Transfers the stack pointer to the X register.
    TSX,
    /// Transfers the X register to the stack pointer.
    TXS,
    /// Pushes the accumulator to the stack.
    PHA,
    /// Pulls the accumulator from the stack.
    PLA,
    /// Pushes the processor status to the stack.
    PHP,
    /// Pulls the processor status from the stack.
    PLP,
    /// Jumps the program counter to a new location.
    ///
    /// # Note
    /// Due to a hardware bug in the original 6502 microprocessor (which is reproduced here for accuracy),
    /// in [AddressMode::AbsoluteIndirect] addressing mode, the high byte will be read from the
    /// start of the current page instead of the next one when the low byte's address is
    /// at the end of a page (i.e. the address mod 256 is 255).
    JMP,
    /// Jumps the program counter to a new location, pushing the current location to the stack.
    JSR,
    /// Pops a return address from the stack and sets the program counter to it.
    RTS,
    /// Handles returning from an interrupt by popping the status and program counter from the stack.
    RTI,
    /// Clears the carry flag.
    CLC,
    /// Sets the carry flag.
    SEC,
    /// Clears the decimal mode flag.
    CLD,
    /// Sets the decimal mode flag.
    SED,
    /// Clears the interrupt disabling flag.
    CLI,
    /// Sets the interrupt disabling flag.
    SEI,
    /// Clears the overflow flag.
    CLV,
    /// Forces a hardware interrupt.
    BRK,
    /// Does nothing.
    NOP,
}

impl Instruction {
    /// Alias for [`Instruction::EOR`] that fits the modern language of calling exclusive or XOR.
    pub const XOR: Instruction = Self::EOR;
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}") // The Debug impl is good for this as well
    }
}

/// A struct representing a ([`Instruction`], [`AddressMode`]) pair as an opcode.
///
/// Not all possible states of this struct are valid opcodes -
/// some may have address modes that are invalid for the instruction.
#[derive(Debug, Copy, Clone, PartialEq, Eq, core::hash::Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Opcode {
    /// The instruction of the opcode.
    pub instruction: Instruction,
    /// The address mode of the opcode if it has one.
    pub address_mode: Option<AddressMode>,
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.instruction)?;
        if let Some(mode) = self.address_mode {
            write!(f, " {mode}")?;
        }
        Ok(())
    }
}

impl Opcode {
    /// Creates a new opcode from an instruction and an addressing mode.
    #[must_use]
    #[inline]
    pub fn new(instruction: Instruction, address_mode: Option<AddressMode>) -> Self {
        Self {
            instruction,
            address_mode,
        }
    }
}

macro_rules! opcodes {
    ($(Opcode::new($inst: ident, $($tt: tt)+) => $repr: literal),* $(,)?) => {
        impl Opcode {
            /// Loads an opcode from a byte slice.
            ///
            /// # Errors
            /// If not enough bytes are supplied, returns an `Err` with the amount of bytes needed.
            /// If the bit pattern is not a valid opcode, returns `Ok(None)`.
            pub fn load(data: &[u8]) -> Result<Option<Opcode>, usize> {
                if data.is_empty() { return Err(1) }
                match data[0] {
                    $($repr => opcodes!(__handle data $inst $($tt)+)),*,
                    _ => Ok(None)
                }
            }

            /// Dumps an opcode into a buffer.
            ///
            /// # Errors
            /// If the opcode is not valid, returns an `Ok(false)`.
            /// If the opcode won't fit in the buffer, returns an `Err` with how many bytes it needs.
            pub fn dump(&self, buf: &mut [u8]) -> Result<bool, usize> {
                if buf.is_empty() { return Err(1) }
                $(opcodes!{__dump self $inst buf $repr $($tt)+})*
                Ok(false)
            }
        }
    };
    (__handle $data: ident $inst: ident None) => {
        Ok(Some(Opcode::new(Instruction::$inst, None)))
    };
    (__handle $data: ident $inst: ident Some(Accumulator)) => {
        Ok(Some(Opcode::new(Instruction::$inst, Some(AddressMode::Accumulator))))
    };
    (__handle $data: ident $inst: ident Some(Immediate)) => {
        opcodes!(__handle_u8 $data $inst Immediate)
    };
    (__handle $data: ident $inst: ident Some(Absolute)) => {
        opcodes!(__handle_u16 $data $inst Absolute)
    };
    (__handle $data: ident $inst: ident Some(ZeroPage)) => {
        opcodes!(__handle_u8 $data $inst ZeroPage)
    };
    (__handle $data: ident $inst: ident Some(Relative)) => {{
        let Some(immediate_byte) = $data.get(1) else { return Err(2) };
        Ok(Some(Opcode::new(Instruction::$inst, Some(AddressMode::Relative(*immediate_byte as i8)))))
    }};
    (__handle $data: ident $inst: ident Some(AbsoluteIndirect)) => {
        opcodes!(__handle_u16 $data $inst AbsoluteIndirect)
    };
    (__handle $data: ident $inst: ident Some(AbsoluteX)) => {
        opcodes!(__handle_u16 $data $inst AbsoluteX)
    };
    (__handle $data: ident $inst: ident Some(AbsoluteY)) => {
        opcodes!(__handle_u16 $data $inst AbsoluteY)
    };
    (__handle $data: ident $inst: ident Some(ZeroPageX)) => {
        opcodes!(__handle_u8 $data $inst ZeroPageX)
    };
    (__handle $data: ident $inst: ident Some(ZeroPageY)) => {
        opcodes!(__handle_u8 $data $inst ZeroPageY)
    };
    (__handle $data: ident $inst: ident Some(ZeroPageIndirectX)) => {
        opcodes!(__handle_u8 $data $inst ZeroPageIndirectX)
    };
    (__handle $data: ident $inst: ident Some(ZeroPageYIndirect)) => {
        opcodes!(__handle_u8 $data $inst ZeroPageYIndirect)
    };

    (__dump $self: ident $inst: ident $buf: ident $repr: literal None) => {
        if let Opcode {instruction: Instruction::$inst, address_mode: None} = $self {
            $buf[0] = $repr;
            return Ok(true);
        };
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(Accumulator)) => {
        if let Opcode {instruction: Instruction::$inst, address_mode: Some(AddressMode::Accumulator)} = $self {
            $buf[0] = $repr;
            return Ok(true);
        };
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(Immediate)) => {
        opcodes!{__dump_u8 $self $inst $buf $repr Immediate}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(Absolute)) => {
        opcodes!{__dump_u16 $self $inst $buf $repr Absolute}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(ZeroPage)) => {
        opcodes!{__dump_u8 $self $inst $buf $repr ZeroPage}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(Relative)) => {
        if let Opcode {instruction: Instruction::$inst, address_mode: Some(AddressMode::Relative(v))} = $self {
            if $buf.len() > 2 { return Err(2) }
            $buf[0] = $repr;
            $buf[1] = *v as u8;
            return Ok(true);
        };
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(AbsoluteIndirect)) => {
        opcodes!{__dump_u16 $self $inst $buf $repr AbsoluteIndirect}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(AbsoluteX)) => {
        opcodes!{__dump_u16 $self $inst $buf $repr AbsoluteX}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(AbsoluteY)) => {
        opcodes!{__dump_u16 $self $inst $buf $repr AbsoluteY}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(ZeroPageX)) => {
        opcodes!{__dump_u8 $self $inst $buf $repr ZeroPageX}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(ZeroPageY)) => {
        opcodes!{__dump_u8 $self $inst $buf $repr ZeroPageY}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(ZeroPageIndirectX)) => {
        opcodes!{__dump_u8 $self $inst $buf $repr ZeroPageIndirectX}
    };
    (__dump $self: ident $inst: ident $buf: ident $repr: literal Some(ZeroPageYIndirect)) => {
        opcodes!{__dump_u8 $self $inst $buf $repr ZeroPageYIndirect}
    };

    (__handle_u8 $data: ident $inst: ident $name: ident) => {{
        let Some(immediate_byte) = $data.get(1) else { return Err(2) };
        Ok(Some(Opcode::new(Instruction::$inst, Some(AddressMode::$name(*immediate_byte)))))
    }};
    (__handle_u16 $data: ident $inst: ident $name: ident) => {{
        let [Some(absolute_1), Some(absolute_2)] = [$data.get(1), $data.get(2)]
            else { return Err(3) };
        Ok(Some(Opcode::new(Instruction::$inst, Some(AddressMode::$name(
            u16::from_le_bytes([*absolute_1, *absolute_2])
        )))))
    }};

    (__dump_u8 $self: ident $inst: ident $buf: ident $repr: literal $name: ident) => {
        if let Opcode {instruction: Instruction::$inst, address_mode: Some(AddressMode::$name(v))} = $self {
            if $buf.len() > 2 { return Err(2) }
            $buf[0] = $repr;
            $buf[1] = *v;
            return Ok(true);
        };
    };
    (__dump_u16 $self: ident $inst: ident $buf: ident $repr: literal $name: ident) => {
        if let Opcode {instruction: Instruction::$inst, address_mode: Some(AddressMode::$name(v))} = $self {
            if $buf.len() > 3 { return Err(3) }
            let [low, high] = v.to_le_bytes();
            $buf[0] = $repr;
            $buf[1] = low;
            $buf[2] = high;
            return Ok(true);
        };
    }
}

opcodes! {
    Opcode::new(BRK, None) => 0x00,
    Opcode::new(ORA, Some(ZeroPageIndirectX)) => 0x01,
    Opcode::new(ORA, Some(ZeroPage)) => 0x05,
    Opcode::new(ASL, Some(ZeroPage)) => 0x06,
    Opcode::new(PHP, None) => 0x08,
    Opcode::new(ORA, Some(Immediate)) => 0x09,
    Opcode::new(ASL, Some(Accumulator)) => 0x0A,
    Opcode::new(ORA, Some(Absolute)) => 0x0D,
    Opcode::new(ASL, Some(Absolute)) => 0x0E,
    Opcode::new(BPL, Some(Relative)) => 0x10,
    Opcode::new(ORA, Some(ZeroPageYIndirect)) => 0x11,
    Opcode::new(ORA, Some(ZeroPageX)) => 0x15,
    Opcode::new(ASL, Some(ZeroPageX)) => 0x16,
    Opcode::new(CLC, None) => 0x18,
    Opcode::new(ORA, Some(AbsoluteY)) => 0x19,
    Opcode::new(ORA, Some(AbsoluteX)) => 0x1D,
    Opcode::new(ASL, Some(AbsoluteX)) => 0x1E,
    Opcode::new(JSR, Some(Absolute)) => 0x20,
    Opcode::new(AND, Some(ZeroPageIndirectX)) => 0x21,
    Opcode::new(BIT, Some(ZeroPage)) => 0x24,
    Opcode::new(AND, Some(ZeroPage)) => 0x25,
    Opcode::new(ROL, Some(ZeroPage)) => 0x26,
    Opcode::new(PLP, None) => 0x28,
    Opcode::new(AND, Some(Immediate)) => 0x29,
    Opcode::new(ROL, Some(Accumulator)) => 0x2A,
    Opcode::new(BIT, Some(Absolute)) => 0x2C,
    Opcode::new(AND, Some(Absolute)) => 0x2D,
    Opcode::new(ROL, Some(Absolute)) => 0x2E,
    Opcode::new(BMI, Some(Relative)) => 0x30,
    Opcode::new(AND, Some(ZeroPageYIndirect)) => 0x31,
    Opcode::new(AND, Some(ZeroPageX)) => 0x35,
    Opcode::new(ROL, Some(ZeroPageX)) => 0x36,
    Opcode::new(SEC, None) => 0x38,
    Opcode::new(AND, Some(AbsoluteY)) => 0x39,
    Opcode::new(AND, Some(AbsoluteX)) => 0x3D,
    Opcode::new(ROL, Some(AbsoluteX)) => 0x3E,
    Opcode::new(RTI, None) => 0x40,
    Opcode::new(EOR, Some(ZeroPageIndirectX)) => 0x41,
    Opcode::new(EOR, Some(ZeroPage)) => 0x45,
    Opcode::new(LSR, Some(ZeroPage)) => 0x46,
    Opcode::new(PHA, None) => 0x48,
    Opcode::new(EOR, Some(Immediate)) => 0x49,
    Opcode::new(LSR, Some(Accumulator)) => 0x4A,
    Opcode::new(JMP, Some(Absolute)) => 0x4C,
    Opcode::new(EOR, Some(Absolute)) => 0x4D,
    Opcode::new(LSR, Some(Absolute)) => 0x4E,
    Opcode::new(BVC, Some(Relative)) => 0x50,
    Opcode::new(EOR, Some(ZeroPageYIndirect)) => 0x51,
    Opcode::new(EOR, Some(ZeroPageX)) => 0x55,
    Opcode::new(LSR, Some(ZeroPageX)) => 0x56,
    Opcode::new(CLI, None) => 0x58,
    Opcode::new(EOR, Some(AbsoluteY)) => 0x59,
    Opcode::new(EOR, Some(AbsoluteX)) => 0x5D,
    Opcode::new(LSR, Some(AbsoluteX)) => 0x5E,
    Opcode::new(RTS, None) => 0x60,
    Opcode::new(ADC, Some(ZeroPageIndirectX)) => 0x61,
    Opcode::new(ADC, Some(ZeroPage)) => 0x65,
    Opcode::new(ROR, Some(ZeroPage)) => 0x66,
    Opcode::new(PLA, None) => 0x68,
    Opcode::new(ADC, Some(Immediate)) => 0x69,
    Opcode::new(ROR, Some(Accumulator)) => 0x6A,
    Opcode::new(JMP, Some(AbsoluteIndirect)) => 0x6C,
    Opcode::new(ADC, Some(Absolute)) => 0x6D,
    Opcode::new(ROR, Some(Absolute)) => 0x6E,
    Opcode::new(BVS, Some(Relative)) => 0x70,
    Opcode::new(ADC, Some(ZeroPageYIndirect)) => 0x71,
    Opcode::new(ADC, Some(ZeroPageX)) => 0x75,
    Opcode::new(ROR, Some(ZeroPageX)) => 0x76,
    Opcode::new(SEI, None) => 0x78,
    Opcode::new(ADC, Some(AbsoluteY)) => 0x79,
    Opcode::new(ADC, Some(AbsoluteX)) => 0x7D,
    Opcode::new(ROR, Some(AbsoluteX)) => 0x7E,
    Opcode::new(STA, Some(ZeroPageIndirectX)) => 0x81,
    Opcode::new(STY, Some(ZeroPage)) => 0x84,
    Opcode::new(STA, Some(ZeroPage)) => 0x85,
    Opcode::new(STX, Some(ZeroPage)) => 0x86,
    Opcode::new(DEY, None) => 0x88,
    Opcode::new(BIT, Some(Immediate)) => 0x89,
    Opcode::new(TXA, None) => 0x8A,
    Opcode::new(STY, Some(Absolute)) => 0x8C,
    Opcode::new(STA, Some(Absolute)) => 0x8D,
    Opcode::new(STX, Some(Absolute)) => 0x8E,
    Opcode::new(BCC, Some(Relative)) => 0x90,
    Opcode::new(STA, Some(ZeroPageYIndirect)) => 0x91,
    Opcode::new(STY, Some(ZeroPageX)) => 0x94,
    Opcode::new(STA, Some(ZeroPageX)) => 0x95,
    Opcode::new(STX, Some(ZeroPageY)) => 0x96,
    Opcode::new(TYA, None) => 0x98,
    Opcode::new(STA, Some(AbsoluteY)) => 0x99,
    Opcode::new(TXS, None) => 0x9A,
    Opcode::new(STA, Some(AbsoluteX)) => 0x9D,
    Opcode::new(LDY, Some(Immediate)) => 0xA0,
    Opcode::new(LDA, Some(ZeroPageIndirectX)) => 0xA1,
    Opcode::new(LDX, Some(Immediate)) => 0xA2,
    Opcode::new(LDY, Some(ZeroPage)) => 0xA4,
    Opcode::new(LDA, Some(ZeroPage)) => 0xA5,
    Opcode::new(LDX, Some(ZeroPage)) => 0xA6,
    Opcode::new(TAY, None) => 0xA8,
    Opcode::new(LDA, Some(Immediate)) => 0xA9,
    Opcode::new(TAX, None) => 0xAA,
    Opcode::new(LDY, Some(Absolute)) => 0xAC,
    Opcode::new(LDA, Some(Absolute)) => 0xAD,
    Opcode::new(LDX, Some(Absolute)) => 0xAE,
    Opcode::new(BCS, Some(Relative)) => 0xB0,
    Opcode::new(LDA, Some(ZeroPageYIndirect)) => 0xB1,
    Opcode::new(LDY, Some(ZeroPageX)) => 0xB4,
    Opcode::new(LDA, Some(ZeroPageX)) => 0xB5,
    Opcode::new(LDX, Some(ZeroPageY)) => 0xB6,
    Opcode::new(CLV, None) => 0xB8,
    Opcode::new(LDA, Some(AbsoluteY)) => 0xB9,
    Opcode::new(TSX, None) => 0xBA,
    Opcode::new(LDY, Some(AbsoluteX)) => 0xBC,
    Opcode::new(LDA, Some(AbsoluteX)) => 0xBD,
    Opcode::new(LDX, Some(AbsoluteY)) => 0xBE,
    Opcode::new(CPY, Some(Immediate)) => 0xC0,
    Opcode::new(CMP, Some(ZeroPageIndirectX)) => 0xC1,
    Opcode::new(CPY, Some(ZeroPage)) => 0xC4,
    Opcode::new(CMP, Some(ZeroPage)) => 0xC5,
    Opcode::new(DEC, Some(ZeroPage)) => 0xC6,
    Opcode::new(INY, None) => 0xC8,
    Opcode::new(CMP, Some(Immediate)) => 0xC9,
    Opcode::new(DEX, None) => 0xCA,
    Opcode::new(CPY, Some(Absolute)) => 0xCC,
    Opcode::new(CMP, Some(Absolute)) => 0xCD,
    Opcode::new(DEC, Some(Absolute)) => 0xCE,
    Opcode::new(BNE, Some(Relative)) => 0xD0,
    Opcode::new(CMP, Some(ZeroPageYIndirect)) => 0xD1,
    Opcode::new(CMP, Some(ZeroPageX)) => 0xD5,
    Opcode::new(DEC, Some(ZeroPageX)) => 0xD6,
    Opcode::new(CLD, None) => 0xD8,
    Opcode::new(CMP, Some(AbsoluteY)) => 0xD9,
    Opcode::new(CMP, Some(AbsoluteX)) => 0xDD,
    Opcode::new(DEC, Some(AbsoluteX)) => 0xDE,
    Opcode::new(CPX, Some(Immediate)) => 0xE0,
    Opcode::new(SBC, Some(ZeroPageIndirectX)) => 0xE1,
    Opcode::new(CPX, Some(ZeroPage)) => 0xE4,
    Opcode::new(SBC, Some(ZeroPage)) => 0xE5,
    Opcode::new(INC, Some(ZeroPage)) => 0xE6,
    Opcode::new(INX, None) => 0xE8,
    Opcode::new(SBC, Some(Immediate)) => 0xE9,
    Opcode::new(NOP, None) => 0xEA,
    Opcode::new(CPX, Some(Absolute)) => 0xEC,
    Opcode::new(SBC, Some(Absolute)) => 0xED,
    Opcode::new(INC, Some(Absolute)) => 0xEE,
    Opcode::new(BEQ, Some(Relative)) => 0xF0,
    Opcode::new(SBC, Some(ZeroPageYIndirect)) => 0xF1,
    Opcode::new(SBC, Some(ZeroPageX)) => 0xF5,
    Opcode::new(INC, Some(ZeroPageX)) => 0xF6,
    Opcode::new(SED, None) => 0xF8,
    Opcode::new(SBC, Some(AbsoluteY)) => 0xF9,
    Opcode::new(SBC, Some(AbsoluteX)) => 0xFD,
    Opcode::new(INC, Some(AbsoluteX)) => 0xFE,
}
