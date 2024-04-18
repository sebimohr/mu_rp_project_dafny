# Sumplete Project

To run the project, just run `make` in the terminal in the current directory.

## Approach to the game

To design the game for verification, I split it into many different methods.
All actions, that alter the grid automatically trigger methods to:

- recalculate the sums of the rows and the columns
- compare the sums to the target sums
- return the game state, so if the game is won or lost

This design allows to only validate small parts, like what should the output be when the a certain field is selected or unselected.
Also in this design dafny knows exactly which elements get edited by a method and which won't.

All the methods for my game require the `Valid()` predicate to be true before and after the method, which tells the verifier that all dimensions of the playing grid are of the same size, as well as the sum arrays.

## Drawbacks

In the beginning on working on my sumplete code, I tried to have many different objects for the grid and the sums.
This introduced problems with verification and accessing the different attributes of the objects in each method.
After trying to make it work and failing, I switched to a more primitive solution by only having one data structure (the `Grid`), which includes all methods and all attributes needed for the game.

Also as my laptop is running Linux, which makes .NET applications kinda slow, I often had the problem of dafny displaying error messages but not reporting any or not running at all, which also got better when switching to a single data structure but still was kind of a mess...

What also was a big problem for me was to introduce a random number generator into the application to make the start grid random in the beginning.
I solved this by introducing an external method, which runs in C#.
