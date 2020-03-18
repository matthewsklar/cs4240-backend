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