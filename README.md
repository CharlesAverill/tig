# Timing Invariant Generation

### Running

Given:
```c
// prog.c
int func(int x) {
    if (x < 0)
        return -1;
    else if (x == 0)
        return 0;
    else if (x > 0)
        return 1;
}

void main() {}
```

Run:
```bash
riscv32-unknown-elf-gcc prog.c -march=rv32imd -o prog
poetry run tig prog func
```
to print out a list of angr constraints for each control-flow path.

Invariant generation temporarily disabled

## Install
Build docker image for ghidra headless bb extraction
```
docker build -t ghidra-bbextract .
```
