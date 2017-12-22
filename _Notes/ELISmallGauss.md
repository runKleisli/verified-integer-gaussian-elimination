__Grids__

Suppose you live on a rectangular grid, as Chess pieces live on a grid.

[A grid](https://commons.wikimedia.org/wiki/File:4x4_grid_spanning_tree.svg)

You can move anywhere you want to on it, but like in Asteroids, when you move off the right edge you start over at the left, and when you move off the top edge you start over at the bottom.

[A discrete torus](https://commons.wikimedia.org/wiki/File:2-2-4-4-de-Bruijn-torus.svg)

However, if you think about your sequences of moves, Up Up Up Up Down Left Left Up Up, they also describe moves on an infinite grid.

[Square lattice pic](https://commons.wikimedia.org/wiki/File:Square_grid_graph.svg)

In particular, you can treat those positions on the infinite grid as being the things wrapped around when you go off the edges. The edges can then be treated as forming a rectangular tiling of the infinite grid that resets you in the finite grid when you move past the edges. Alternatively, you can think of the rectangular grid as the 2D grid with these rectangles [glued over in a cycle](https://commons.wikimedia.org/wiki/File:4covering.svg), top edge to bottom, left edge to right.

Let's also assume there's a starting position in the infinite 2D grid from which your motions are recorded. I claim that if you know where the vertical and horizontal line through that starting position wrap around at, you know where every other vertical and horizontal line wrap around at because you just shift those two around, and you actually know where you end up after you wrap around an edge starting at any point and making any motion because every motion breaks down into a sequence of single-step horizontal and vertical moves.



__Harder grids__

Now, what happens if instead of being given a description of the rectangles by the Up and Right points you were given the points Up and the Up Right corner? Can we still recognize what grid it forms?

If you skew the grid so the vertical line through the starting position and Up doesn't move but the one through Up Right and Right does, you can move Up Right back to Up without changing Up. That is, you can use reversible symmetries of space that move both the given points integer amounts at a time to convert weirder grids like [this](https://en.wikipedia.org/wiki/File:Equilateral_Triangle_Lattice.svg) into a form where you can tell what the grid looks like, what points are on it, and what the axes should be.

Integer gaussian elimination gives a simple way to recognize what the lattice is in terms that let you easily say that the corresponding finite grid is 3x5 or 4x10 specifically, by using the right symmetries to convert it into an equivalent one that's easy to describe. 3-by-infinity is also an option, since the two points you wrap around at could lie on the same line, leaving nowhere to wrap around at on the orthogonal line.

That situation comes up often in algebraic topology, where when you go to calculate what holes a space has, part of the problem is the space asks you to figure out what an infinite grid looks like when you wrap it around on an arbitrary lattice. If you can always recognize what that lattice by using the right symmetries, you can get an explicit answer like "It's a 3x5 grid. The two holes are. You can also think of it as one hole, but it's definitively a 3x5 grid." And that has palpable geometric meaning, it's just hard to explain to your friends what that meaning is.



__Movements allowed__

Suppose you live on a grid, as Chess pieces live on a grid.

You can consider a horse move to be an L shape or a straight line through which there are no points between where the horse starts and lands.

Suppose the horse starts in the center of the chessboard, & the chessboard is infinite.

Which of the squares can we reach, what does that pattern look like?

We can move in 8 directions, but half of these are the same direction. During manual gaussian elimination half the 8 starting rows of the matrix could be eliminated immediately.

Are there any places we can reach with those 4 movements, backwards and forwards, that we can't reach with fewer of them? Can we reach every position on the infinite grid with those 4 movements?

Notice that if you take a motion to the left and apply it repeatedly to a position, you move that position to the left.

Let's look at just Up Right Right and Up Up Right.

```
[2R, 1U]
[1R, 2U]
```

If you note the former has only 1 Up step while the latter has 2, you see you can get rid of the double Up in the latter.

This is important, because a double Up and a single Right means a double gap vertically but a single gap horizontally - different grid spacings in the motion. To get rid of the Up Up with Up Right Right you need to go Down Left Left twice from Up Up Right, which gives you (Up Up Right) (Down Left Left) (Down Left Left) = (Right) (Left Left) (Left Left) = Left Left Left.

```
[2R, 1U]
[3L, 0U] = [1R, 2U]-[2R,1U]-[2R,1U]
```

So now you know you can reach Left Left Left and Up Right Right. But if you forgot what motions you were originally allowed to make, you know that you still have one you used to get the positions you have, so you know you can reverse that motion to get back to what motions you had before. This makes starting with Left Left Left and Up Right Right equivalent to starting with Up Up Right and Up Right Right - you get the same grid of possible positions. Only now, one of the motions you make is all horizontal & not the other.

Note this is not the case when you apply a motion to itself! If you move to

```
[0R, 0U] = [2R, 1U] - [2R, 1U]
[3L, 0U]
```

and then forget how to move [2R, 1U], you can only move Left Left Left from then on.

And if you move from there to 6L and forget how to move 3L, you can only move 6 spaces at a time, and can never recover motion in steps of 3. In the math for it, you've multiplied by 2, which is an integer, but you can't then multiply by 1/2 when you can only multiply by integers.

Why we get reversibility (bispannability) outside of those cases is, two grid points A and B being combined into a new pair of grid points A and B-A, one step at a time, so we know we still have the A we make B-A from and can thus use it to get the pair A & (B-A)+A = B.



I think you'll find it's easier to know whether a point on the grid is available to move to now that one of the motions is completely horizontal.

Look:

```
[2R, 1U]
[3L, 0U]
```

That 0 in the corner can't make the 1 in the topright become 0. It's stuck. It's also easy to tell we can't make the other one all vertical - there's no multiple of 3 you can add to 2 to get 0.

We want to create 0s if we want to know things about how many independent axes of motion we have.

The order doesn't matter, which is where the permutations come in - the other elementary row operations.

If we take these points

```
[0, 1, 0]
[2, 3, 4]
[0, 0, 1]
[1, 2, 3]
[0, 0, 1]
```

and we order everything so that the trailing 0s never move to the left

```
[2, 3, 4]
[1, 2, 3]
[0, 1, 0]
[0, 0, 1]
[0, 0, 1]
```

then there's a lowest row to have each nonzero entry, and all rows below it have 0 in that entry.

If we eliminate the top row using the lowest row to have initial entry nonzero, we get

```
[0, -1, 4-6] = [2, 3, 4] - [1, 2, 3] - [1, 2, 3]
[1,  2,   3]
[0,  1,   0]
[0,  0,   1]
[0,  0,   1]
```

Now the row with nonzero initial entry is unique, so no other row can be used to make it 0, and if we move it to the top, we see the real pattern is

```
[1,  2,  3]
[0, -1, -2]
[0,  1,  0]
[0,  0,  1]
[0,  0,  1]
```

Now pretend the first row & column don't exist (you're not getting rid of that first row with all 0s in the intial column).

```
[-1, -2]
[ 1,  0]
[ 0,  1]
[ 0,  1]
```

eliminate

```
[ 0, -2] = [-1,-2] + [1, 0]
[ 1,  0]
[ 0,  1]
[ 0,  1]
```

if you recall the initial columns here it doesn't make a difference, cause all the numbers there are 0.

reorder

```
[ 1,  0]
[ 0, -2]
[ 0,  1]
[ 0,  1]
```

forget

```
[-2]
[1]
[1]
```

eliminate

```
[0]
[0]
[1]
```

reorder

```
[1]
[0]
[0]
```

all done - time to remember.

remember that last row

```
   1,0]
     1]
     0]
     0]
```

and the one before that

```
[1,2,3]
   1,0]
     1]
     0]
     0]
```

and it was all 0s to the left of where we forgot, so it's actually

```
[1,2,3]
[0,1,0]
[0,0,1]
[0,0,0]
[0,0,0]
```

3 distinct axes.
