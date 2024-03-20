# Instructions Part 1 - Sumplete

In this part of your project work you are required to specify, code and verify code to play the game Sumplete (see sumplete.com). The suggested language to use in Dafny, but you are welcome to work with other verifiers e.g. Why3, OpenJML etc.

The board game consists of NxN squares, each containing a number. The game requires that the players deletes numbers so that each row/column adds up to a target number provided at the right of each row/bottom of each column of the board. Examples of the game can be seen at sumplete.com.

The program can be written in any language that has appropriate support for at least preconditions, postconditions, loop invariants and variants. JML and Dafny are suitable choices, with Dafny being the most suitable as we have covered it in class.

Your submission should provide:

(a) a program design (in English/UML/OCL) showing how you have designed the game for verification.

(b) a rational for how you implemented the program e.g. what data structures you used and why

(c) commented code (at least at the method level)

(d) commented assertions explaining what you are expressing and indication what has been verified and what hasn't (comment out anything that does not verify)

(e) any drawbacks/advantages to the approach that you have taken.

Note that the program does not need any interface other than the command line. While you are welcome to collaborate (e.g. play the game and discuss the rules), everyone should submit their own project work and plagiarism will result in a mark of 0% for both the copied and the copier.

A good way to start may be to write methods to identify specs/code for 1*3 grids, then 3*3 grids, then N*N grids:

- does a row sum to the target value

- does a column sum to a target value

- if the row/column does not sum to the target value, can you eliminate numbers in the grid (e.g. replace them by 0) to reach the target value (try rows first, when you try rows and columns together its more complicated)

Think about how you would generate multiple boards, of different sizes. Does your code work for negative values on the board? What assumption have you made about the board?
