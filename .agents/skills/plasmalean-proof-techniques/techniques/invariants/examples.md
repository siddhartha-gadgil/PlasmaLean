# Examples: Invariant Construction

## Example 1: Parity In A Game

**Problem shape:** Show a game position cannot reach a target state.

**Use of technique:**
1. Define an invariant: parity of the number of marked squares.
2. Prove every legal move changes the count by an even number.
3. Compute the parity of the initial state.
4. Show the target state has the opposite parity.

## Example 2: Coloring In A Tiling Problem

**Problem shape:** Prove a board cannot be tiled by dominoes.

**Use of technique:**
1. Color the board in a checkerboard pattern.
2. Observe every domino covers one black and one white square.
3. Count black and white squares in the board.
4. If the counts differ, tiling is impossible.

## Example 3: Monovariant For Termination

**Problem shape:** Show a process must stop.

**Use of technique:**
1. Define an integer-valued quantity that strictly decreases with every move.
2. Prove it is bounded below.
3. Conclude infinite play is impossible.
4. Use the terminal state to prove the required result.

## Fully Explicit Goal Reduction: Mutilated Chessboard

**Statement:** Remove two opposite corner squares from an `8 x 8` chessboard. Prove the remaining board cannot be tiled by `1 x 2` dominoes.

**Goal:** Prove no domino tiling exists.

**Reduction by coloring invariant:**
1. Color the chessboard black and white in the usual checkerboard pattern.
2. Opposite corners have the same color, so removing them leaves `30` squares of one color and `32` of the other.
3. Invariant subgoal: every domino covers exactly one black and one white square.
4. Any domino tiling would therefore cover equal numbers of black and white squares.
5. This contradicts the unequal color counts, so no tiling exists.
