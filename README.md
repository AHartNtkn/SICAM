# SICAM
A parallel general-purpose computer based on interaction combinators.

SICAM stands for "Symmetric Interaction Combinator Assembly Machine"

For the moment, this is just a clash project, but I eventually want to load it onto an FPGA.

See the file `reduce.hs` in the `src` folder of `clash files` for the source code of a family of machines.

The memory consists of a series of nodes describing a graph of connected interaction combinators. Each node has a kind and three link names. The link names are not memory addresses but simply names that are mentioned at most twice throughout memory. There is also an additional bit indicating if the node carries data rather than addresses.

There are currently 11 node kinds.

- `Rot`: the root of a program graph
- `Con`: function application/abstraction
- `Dup`: paring and duplication
- `Era`: garbage collection/deletion
- `Equ`: equation
- `Num`: number
- `Mul`: multiplication
- `Add`: addition
- `If0`: if statement on a number
- `Key`: Reads an input external to the machine
- `Scr`: Writes data into screen memory

Future versions will likely add more; specifically a family of nodes for communicating with external ports. Perhaps also an `Amb` combinator for handling concurrency, but I'm undecided.

Interaction for `Con`, `Dup`, and `Era` proceed exactly how they would in ordinary interaction combinators. To indicate how they would look in memory, here's an example program that defines the S and K combinators and applies SKK to the number 23.

```
Rot 1 0 0 0       -- 1 = Root

Con 2 1 1 3       -- 1 = 2 3  ; SKKN = SKK n
Con 4 1 2 5       -- 2 = 4 5  ; SKK = SK K2
Con 6 1 4 7       -- 4 = 6 7  ; SK = S K1

-- S = \f. \g. \x. f x (g x)
Con 6  1 9  8     -- S = \f . u1
Con 9  1 11 10    -- u1 = \g . u2
Con 11 1 12 13    -- u2 = \x . u3
Dup 13 1 14 15    -- x = {x1, x2}
Con 16 1 12 17    -- u3 = (u4 u5)
Con 8  1 16 14    -- u4 = (f x1)
Con 10 1 17 15    -- u5 = (g x2)

K = \x. \y. x
Con 7  1 19 18    -- K1 = \x . u1
Con 19 1 18 20    -- u1 = \y . x
Era 20 0 0  0     -- y = *

Con 5  1 22 21    -- K2 = ...
Con 22 1 21 23
Era 23 0 0  0

Num 3 0 0 23      -- n = 23
```

The second number in each line is a bit indicating if the last two numbers are addresses. After a few steps of evaluation, the memory will normalize into;

```
Rot 13 0 0 0
Num 13 0 0 23
```

The architecture does this by creating a new array indexed by link names. Each node is then scattered into the index associated with the link in its principal port. This permutation circuit will catch at most two nodes, permuting memory so that interacting nodes are exactly next to each other.

A local interaction circuit is then mapped over this memory creating instructions for altering the current node memory. These instructions are simply addresses where the memory is changed paired with nodes (or empty space) to put at those addresses. These instructions are fed into a scattering circuit which alters the memory.

In this way, the graph can evaluate entirely in parallel.

Some additional nodes are added to allow for more general-purpose computation. Whenever `Key` interacts with a node that expects a number, it reads an input and turns into a `Num` node storing that input. Whenever `Scr` interacts with a number, that number is interpreted as a pixel change.

The arithmetic instructions are a bit more complicated. Since they need two numbers, each two-argument ALU instruction carries a single-bit state indicating if it's seen its first argument already. If it hasn't, the state will change and its principal and secondary ports will swap. If it has, it grabs the number stored at the node that its secondary port points to and executes the expected operation. Here's an example evaluation;

```
Rot  1 0 0 0
Add0 3 1 1 2 
Num  2 0 0 5
Num  3 0 0 7

=>=>=>=>=>=>=

Rot  1 0 0 0
Add1 2 1 1 3 
Num  2 0 0 5
Num  3 0 0 7

=>=>=>=>=>=>=

Rot  1 0 0 0
Num  1 0 0 12 
```
