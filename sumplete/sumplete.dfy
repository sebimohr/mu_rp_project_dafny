/*
Sebastian Mohr - 23141808
Project: Part 1 - Sumplete
*/

module DataStructure {
  /**
  The sumplete grid.
   */
  class Grid {
    // grid_size == n
    ghost var grid_size: int

    // n*n grid -> rows*columns
    var start_grid: array2<int> // grid that gets displayed to the player

    var target_grid: array2<int> // solution to the puzzle
    var target_rows_sum: array<int> // rows sums the player has to fulfill
    var target_columns_sum: array<int> // column sums the player has to fulfill

    var player_grid: array2<int> // grid with the currently chosen numbers, at the beginning all nums are deactivated
    var player_rows_sum: array<int> // rows sum that the player currently has
    var player_columns_sum: array<int> // columns sum that the player currently has

    /**
    Ensures that all grids are the same size and the rows and columns have the correct sizes for the grids.
     */
    ghost predicate Valid()
      reads this
    {
      // ensure all grids have the same n*n size
      grid_size == start_grid.Length0 && grid_size == start_grid.Length1 &&
      grid_size == target_grid.Length0 && grid_size == target_grid.Length1 &&
      grid_size == player_grid.Length0 && grid_size == player_grid.Length1 &&

      // ensure sum arrays have same length as rows & columns
      grid_size == target_rows_sum.Length && grid_size == target_columns_sum.Length &&
      grid_size == player_rows_sum.Length && grid_size == player_columns_sum.Length
    }

    /**
    Instantiates the grids and sums.
     */
    constructor(size: int)
      requires size > 0
      ensures Valid()
    {
      grid_size := size;

      start_grid := new int[size, size]((i, j) => 0);

      target_grid := new int[size, size]((i, j) => 0);
      target_rows_sum := new int[size](i => 0);
      target_columns_sum := new int[size](i => 0);

      player_grid := new int[size, size]((i, j) => 0);
      player_rows_sum := new int[size](i => 0);
      player_columns_sum := new int[size](i => 0);
    }

    /**
    Sets up the game by:
    - filling the start_grid with random numbers
    - filling the target_grid with the chosen numbers
    - calculating the target_(rows/columns)_sums
     */
    method setupGame()
      modifies this, start_grid, target_grid, target_rows_sum, target_columns_sum
      requires Valid()
      ensures Valid()
    {
      var i, j := 0, 0;
      var size := start_grid.Length0;

      while i < size
        invariant size == grid_size
        invariant Valid()
        modifies start_grid, target_grid
      {
        while j < size
          invariant size == grid_size
          invariant Valid()
          modifies start_grid, target_grid
        {
          start_grid[i,j] := random();
          var randomBool := randomBool();
          if randomBool {
            target_grid[i,j] := start_grid[i,j];
          }
          j := j + 1;
        }
        i := i + 1;
      }

      i, j := 0, 0;
      while i < size
        invariant size == grid_size
        invariant Valid()
        modifies target_rows_sum, target_columns_sum
      {
        while j < size
          invariant size == grid_size
          invariant Valid()
          modifies target_rows_sum, target_columns_sum
        {
          var currentNum := target_grid[i,j];
          target_rows_sum[i] := target_rows_sum[i] + currentNum;
          target_columns_sum[j] := target_columns_sum[j] + currentNum;
          j := j + 1;
        }
        i := i + 1;
      }
    }

    /**
    Toggles the field to a value or 0, depending on its previous value.
    Also updates the sums and checks if the game is won.

    @param{row} The row where the field is located.
    @param{column} The column where the field is located.

    @returns{bool} True if the game is won, else false.
     */
    method toggleField(row: nat, column: nat) returns (gameWon: bool)
      modifies this, player_grid, player_rows_sum, player_columns_sum
      requires Valid()
      requires 0 <= row < grid_size && 0 <= column < grid_size
      ensures Valid()
      // ensures old(player_grid[row, column]) == 0 ==> player_grid[row, column] == start_grid[row, column]
      // ensures old(player_grid[row, column]) != 0 ==> player_grid[row, column] == 0
    {
      if player_grid[row, column] == 0 {
        player_grid[row, column] := player_grid[row, column];
      }
      else {
        player_grid[row, column] := 0;
      }

      calculateCurrentPlayerSums();
      gameWon := determineGameState();
    }

    /**
    Calculates the current sum of each player_(rows/columns)_sum.
     */
    method calculateCurrentPlayerSums()
      modifies this, player_rows_sum, player_columns_sum
      requires Valid()
      ensures Valid()
    {
      var i, j := 0, 0;
      var size := player_grid.Length0;

      while i < size
        invariant size == grid_size
        invariant Valid()
        modifies player_rows_sum, player_columns_sum
      {
        while j < size
          invariant size == grid_size
          invariant Valid()
          modifies player_rows_sum, player_columns_sum
        {
          var currentNum := player_grid[i,j];
          player_rows_sum[i] := player_rows_sum[i] + currentNum;
          player_columns_sum[j] := player_columns_sum[j] + currentNum;
          j := j + 1;
        }
        i := i + 1;
      }
    }

    /**
    Checks if game is won with the current player_grid.

    @returns{bool} True if the game is won, else false.
     */
    method determineGameState() returns (isGameWon: bool)
      requires Valid()
      ensures Valid()
    {
      var i := 0;
      isGameWon := true;

      while i < player_rows_sum.Length
        invariant Valid()
      {
        if(player_rows_sum[i] != target_rows_sum[i] ||
           player_columns_sum[i] != target_columns_sum[i]) {
          isGameWon := false;
        }
        i := i + 1;
      }
    }

    /**
    Random number generator.

    @returns{int} Random number between 1 and 9.
    */
    method random() returns (randomNumber: nat)
      ensures 1 <= randomNumber <= 9
    {
      var numberSet := {1, 2, 3, 4, 5, 6, 7, 8, 9};
      randomNumber :| randomNumber in numberSet;
    }

    /**
    Random boolean generator.

    @returns{bool} Random boolean.
    */
    method randomBool() returns (randomBool: bool)
    {
      var boolSet: set<bool> := {true, false};
      randomBool :| randomBool in boolSet;
    }
  }
}

module Game {
  import dataStructure = DataStructure

  /**
  Sets up the game with a random grid of size given and sums for all rows and columns.
   */
  method setupGame(size: nat) returns (grid: dataStructure.Grid)
    requires size > 0
  {
    grid := new dataStructure.Grid(size);
  }
}
