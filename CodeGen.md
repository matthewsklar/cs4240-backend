## Calling convention

* First 4 args passed in $a0..$a3
* Remainder of args passed on stack, with arg 5 @ [$sp], arg 6 @ [$sp + 4], etc.
* Return value passed in $v0
* Return address in $ra (saved by caller)
* $t0..$t9 saved by caller
* $s0..$s7 saved by callee (but if we never use these, no need to actually save)

## Register allocation

The following registers are available for allocation:
* $t0..$t9 (caller must save these)
* $v1 (be careful w/ outside functions that return 2 results)
* $s0..$s7 (no need to save these if we generate the proper prologs/epilogs)
* $at (caller save)
* $k0..$k1 (kernel registers... be careful)
* $gp (global pointer, do we need this in our generated code?)

In terms of spilling, we also need some free registers to work with! For example, imagine
the following TigerIR code getting spilled:
  `add a, b, c`
This maps to the `add` MIPS32 instruction, which takes 2 source registers and writes to one
destination register. In this case, a sane approach is:
  ```
  lw $at, __b($fp)
  lw $v1, __c($fp)
  add $at, $at, $v1
  sw $at, __a($fp)
  ```
Note that due to the way spilling works, the values stored in the registers can reflect a newer
value than the stack-saved value if and only if we're in the middle of an operation. While we
could fuse two spills to the same variable, this requires us to save the $at and $v1 registers
to the stack when calling functions, and we'll rarely want to do this. It's also just more work
to deal with. So in this scenario, we can choose to never save these two temporary spill registers.

## Stack frame layout

       arg n         -- This is the opposite of what is normally done, but it's useful to index
       ...           -- args as [$fp-4*i]. Reasoning-first push args then build stack in callee
       arg 5
       ...           -- Typically, 4 extra slots are created for storing args 1..4, do we need this?
[$fp]: saved $fp
       saved $ra
       $s0           -- + other saved registers
       ...
       $s7
       local 0
       ...
[$sp]: local n

Design choice: we can ignore the 8-byte alignment suggested for MIPS32 since we never use 64-bit
types (doubles or long longs).

We can also choose to allocate 4 extra arg locations for saving args to the stack: if we need to
spill a variable, it's useful to have a statically-assigned position to spill it to (this is
already true for the other args + locals). If we create slots for each argument, then every variable
(barring temps in the middle of an operation) should have a correct position on the stack. The question
is whether this is a useful property to have?

## Note on arrays

We choose to statically allocate every array as a local on the stack. This means 3 things:
1) to pass an array to a function, we need to pass a pointer
2) we always have an immediate value that can be used for the array when calling a function
  2.5) our code assumes that all array bases are stored in registers, so this should be fine
       from the callee's side as well
3) we can't (directly) return arrays allocated on the stack (even though TigerIR allows this)
