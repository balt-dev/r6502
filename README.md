[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/balt-dev/r6502/.github%2Fworkflows%2Frust.yml?branch=trunk&style=flat&label=tests)](https://github.com/balt-dev/r6502/actions/)
[![Documentation](https://docs.rs/r6502/badge.svg)](https://docs.rs/r6502)
[![MSRV](https://img.shields.io/badge/MSRV-1.66.1-gold)](https://gist.github.com/alexheretic/d1e98d8433b602e57f5d0a9637927e0c)
[![Repository](https://img.shields.io/badge/-GitHub-%23181717?style=flat&logo=github&labelColor=%23555555&color=%23181717)](https://github.com/balt-dev/r6502)
[![Latest version](https://img.shields.io/crates/v/r6502.svg)](https://crates.io/crates/r6502)
[![License](https://img.shields.io/crates/l/r6502.svg)](https://github.com/balt-dev/r6502/blob/trunk/LICENSE-MIT)
[![unsafe forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)
![Maintenance](https://img.shields.io/maintenance/as-is/2024?color=gold)
# r6502

### Yet another NMOS 6502 emulator.
  
---  

Designed to support `no-std` and not require an allocator nor any unsafe code, and be reasonably fast.

The API of this crate shies away from implementing interrupt handling,   
instead having you step the emulator one opcode at a time and handle them yourself.

## Feature Flags
The following feature flags exist:  

| Name      | Description                                                                                                                                                                                                  |  
|-----------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|  
| bcd       | Enable binary-coded decimal arithmetic.<br/>Enabled by default. Disable if you're writing a NES emulator.<br/>Note that invalid BCD is left untested and will not function faithfully to the NMOS 6502.      |  
| bytemuck  | Enables [bytemuck](https://docs.rs/bytemuck/) support.                                                                                                                                                       |  
| arbitrary | Enables [arbitrary](https://docs.rs/arbitrary/) support. This will pull in `std`.                                                                                                                            |  
| serde     | Enables [serde](https://docs.rs/serde) support.                                                                                                                                                              |  
| hashbrown | Enables [hashbrown](https://docs.rs/hashbrown) support.                                                                                                                                                      |

## Example
```rust ignore  
extern crate std;

use std::eprintln;

use r6502::{Emulator, FunctionReadCallback, FunctionWriteCallback};

fn main() {
    let mut emu = Emulator::default()
        .with_read_callback(FunctionReadCallback(|state: &mut State, addr| {
            // Log reads  
            eprintln!("Read from #${addr:04x}");
            state.memory[addr as usize]
        }))
        .with_write_callback(FunctionWriteCallback(|state: &mut State, addr, byte|
            // Don't write to ROM 
            if addr < 0xFF00 {
                state.memory[addr as usize] = byte
            })
        )
        .with_rom(include_bytes!("rom.bin"))
        .with_program_counter(0x200);

    loop {
        let interrupt_requested = emu.step()
            .expect("found an invalid opcode (only NMOS 6502 opcodes are supported)");
        if interrupt_requested { // Go to IRQ interrupt vector 
            let vector = u16::from_le_bytes([
                emu.read(0xFFFE),
                emu.read(0xFFFF)
            ]);
            emu.state.program_counter = vector;
        }
    }
}
```

---
## Licensing

This may be licensed under either the MIT or Apache-2.0 license, at your option.
