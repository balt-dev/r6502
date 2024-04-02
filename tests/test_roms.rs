extern crate std;

use r6502::*;

#[test]
fn all_suite_a() -> Result<(), usize> {
    static TEST_BIN: &[u8] = include_bytes!("AllSuiteA.bin");

    let mut emulator = Emulator::default()
        .with_program_counter(0x4000)
        .with_rom_from(TEST_BIN, 0x4000);
    let mut last_pc;
    loop {
        last_pc = emulator.state.program_counter;
        let needs_interrupt = emulator.step().unwrap();
        if emulator.state.program_counter == last_pc {
            let trap_number = emulator.state.memory[0x0210];
            if trap_number != 0xFF {
                eprintln!("!!! ENTERED TRAP !!!");
                eprintln!("{:02x?}", emulator.state);
                eprintln!("Failed test: {trap_number}",);
                return Err(0);
            }
            break;
        }
        if needs_interrupt {
            eprintln!("!!! ENTERED INTERRUPT !!!");
            eprintln!("{:02x?}", emulator.state);
            return Err(0);
        }
    }
    Ok(())
}

#[test]
fn functional_test() -> Result<(), usize> {
    static TEST_BIN: &[u8; 65536] = include_bytes!("6502_functional_test.bin");

    let mut emulator = Emulator::default()
        .with_program_counter(0x400)
        .with_rom(*TEST_BIN);
    let mut last_pc;
    loop {
        last_pc = emulator.state.program_counter;
        let needs_interrupt = emulator.step().unwrap();
        if emulator.state.program_counter == last_pc {
            if last_pc == 0x3469 {
                // https://github.com/Klaus2m5/6502_65C02_functional_tests/blob/master/bin_files/6502_functional_test.lst#L13377C1-L13377C5
                // Success!
                return Ok(());
            }
            eprintln!("!!! ENTERED TRAP !!!");
            eprintln!("{:02x?}", emulator.state);
            eprintln!("--------------------------[ZERO PAGE]---------------------------");
            for i in 0..16 {
                eprintln!("{:02x?}", &emulator.state.memory[i * 16..(i + 1) * 16])
            }
            eprintln!("----------------------------[STACK]-----------------------------");
            for i in 0..16 {
                eprintln!(
                    "{:02x?}",
                    &emulator.state.memory[0x100 + (i * 16)..0x100 + ((i + 1) * 16)]
                )
            }
            return Err(0);
        }
        if needs_interrupt {
            let vector = u16::from_le_bytes([emulator.read(0xFFFE), emulator.read(0xFFFF)]);
            eprintln!("[MASKABLE INTERRUPT, GOING TO IRQ VECTOR @ {vector:02X}]");
            // Go to interrupt vector
            emulator.state.program_counter = vector;
        }
    }
}
