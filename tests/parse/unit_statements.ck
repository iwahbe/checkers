module unit_statements

# D35: `Unit` calls may stand alone; the type checker (M1) rejects non-Unit ones.
fn greet term
    terminal.print_line "hello" term
    terminal.print_line "world" term
    let _ = compute 1
    0
