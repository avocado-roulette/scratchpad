# scratchpad
Miscellaneous scripts and ad-hoc code

## AvocadoRouletteScratchpad Examples

Run `lake update` from the root of the repo to pull the dependencies.

### SixNineThree

**Theorem.** For any number in the 7 times table that ends in a 3, you can insert a 9
in 2nd place (i.e., the 10s column) and the number will still be in the 7 times table.

e.g.

- `63 -> 693 -> 6993`
- `133 -> 1393 -> 13993`

Couple of comments:

- This is not a deep theorem, just an exercise at converting a simple idea into
  a lean proof.
- We can generalize this in a couple of directions as simple exercises:
  - Numbers in the 7 times table that end in a 1, you can insert a 3 similarly.
  - Numbers in the 7 times table that end in a 2, you can insert a 6 similarly.
  - For a number in the x times table, if n ends in 10 - x, you can insert 9s
    similarly.
