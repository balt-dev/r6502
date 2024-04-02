#![no_std]
#![warn(missing_docs, clippy::pedantic, clippy::perf)]
#![allow(clippy::type_complexity, clippy::missing_panics_doc)]
#![forbid(unsafe_code)]
#![doc = include_str!("../README.md")]

pub mod state;
pub mod instructions;
pub mod emulation;

pub use instructions::{Opcode, Instruction, AddressMode};
pub use state::{State, Status};
pub use emulation::{Emulator, ReadCallback, WriteCallback, DefaultReadCallback, DefaultWriteCallback, FunctionReadCallback, FunctionWriteCallback};
