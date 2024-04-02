//! Holds the structs pertaining to the state of the emulator.
#[cfg(feature = "arbitrary")]
extern crate std;

#[cfg(feature = "serde")]
use {
    serde::{Serialize, Deserialize},
    serde_with::{As, Bytes}
};

#[derive(Copy, Clone, PartialEq, Eq, core::hash::Hash)]
#[cfg_attr(feature = "bytemuck", derive(bytemuck::Pod, bytemuck::Zeroable))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
/// A full representation of the state of the emulator.
///
/// # Note
/// This struct is quite large. It's not advised to leave this on the stack if you have an allocator.
#[repr(C)]
pub struct State {
    /// The current program counter of the emulator.
    pub program_counter: u16,
    /// The current state of the accumulator in the emulator.
    pub accumulator: u8,
    /// The current state of the X register in the emulator.
    pub x_register: u8,
    /// The current state of the Y register in the emulator.
    pub y_register: u8,
    /// The current stack pointer of the emulator.
    pub stack_pointer: u8,
    /// The emulator's status flags.
    pub status: Status,
    #[doc(hidden)]
    #[cfg_attr(feature = "serde", serde(skip))]
    _padding: u8,
    /// The emulator's memory, left as one contiguous array of bytes.
    ///
    /// This is stored inside the struct to prevent needing an allocator,
    /// but grows the struct's size considerably.
    /// Consider storing this struct on the heap if this is undesirable and you have one.
    #[cfg_attr(feature = "serde", serde(with = "As::<Bytes>"))]
    pub memory: [u8; 256 * 256]
}

#[allow(clippy::missing_fields_in_debug)]
impl core::fmt::Debug for State {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("State")
            .field("accumulator", &self.accumulator)
            .field("x_register", &self.x_register)
            .field("y_register", &self.y_register)
            .field("program_counter", &self.program_counter)
            .field("stack_pointer", &self.stack_pointer)
            .field("status", &self.status)
            .finish()
    }
}

impl Default for State {
    fn default() -> Self {
        State {
            accumulator: 0,
            x_register: 0,
            y_register: 0,
            program_counter: 0x200,
            stack_pointer: 0xFF,
            status: Status::default(),
            memory: [0; 256 * 256],
            _padding: 0
        }
    }
}

mod flags {
    #![allow(missing_docs)] // shut up
    #[cfg(feature = "arbitrary")]
    extern crate std;

    bitflags::bitflags! {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, core::hash::Hash)]
        #[cfg_attr(feature = "bytemuck", derive(bytemuck::Pod, bytemuck::Zeroable))]
        #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
        #[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
        #[repr(transparent)]
        /// A [bitflags]-based representation of the status flags of a 6502 microprocessor.
        pub struct Status: u8 {
            const NEGATIVE          = 0b1000_0000;
            const OVERFLOW          = 0b0100_0000;
            const UNUSED            = 0b0010_0000;
            const BREAK             = 0b0001_0000;
            const DECIMAL           = 0b0000_1000;
            const INTERRUPT_DISABLE = 0b0000_0100;
            const ZERO              = 0b0000_0010;
            const CARRY             = 0b0000_0001;
        }
    }

    impl Default for Status {
        fn default() -> Self {
            Status::UNUSED | Status::INTERRUPT_DISABLE | Status::ZERO
        }
    }
}

pub use flags::Status;
