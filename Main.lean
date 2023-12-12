
def main : List String → IO Unit
| [] => IO.println s!"Expects one argument"
| h::[] => IO.println s!"Hello! {h}"
| _::t => IO.println s!"Too many args {t} ignored"
