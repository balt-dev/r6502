#![no_std]
#![warn(missing_docs, clippy::pedantic, clippy::perf)]
#![allow(clippy::type_complexity, clippy::missing_panics_doc)]
#![forbid(unsafe_code)]
#![doc = include_str!("../README.md")]

pub mod emulation;
pub mod instructions;
pub mod state;

pub use emulation::{
    DefaultCallbacks, Emulator, FunctionReadCallback,
    FunctionWriteCallback, ReadCallback, WriteCallback,
};
pub use instructions::{AddressMode, Instruction, Opcode};
pub use state::{State, Status};
