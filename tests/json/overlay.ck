module overlay

# On disk this file is fine; overlay.overlay replaces it and lib/helper.ck
# with unsaved text that has errors, so the diagnostics are about that text.
import lib.helper

fn f -> r : r~Nat
    helper.one
