/*
Sebastian Mohr - 23141808
Project: Part 1 - Sumplete
*/

module DataStructure {
  /**
  The sumplete grid.
   */
  class Grid {
    // n*n grid -> rows*columns
    var start_grid: array2<int>
    var target_grid: array2<int>
    var target_rows_sum: array<int>
    var target_columns_sum: array<int>

    // n*n grid -> rows*columns
    var player_grid: array2<int>
    var player_rows_sum: array<int>
    var player_columns_sum: array<int>

    predicate Valid()
      reads this
      reads start_grid
      reads target_grid, target_rows_sum, target_columns_sum
      reads player_grid, player_rows_sum, player_columns_sum
    {
      // ensure n*n grid
      start_grid.Length0 == start_grid.Length1 &&

      // ensure start_grid, target_grid and player_grid have the same size
      start_grid.Length0 == target_grid.Length0 && start_grid.Length1 == target_grid.Length1 &&
      start_grid.Length0 == player_grid.Length0 && start_grid.Length1 == player_grid.Length1 &&

      // ensure sum arrays have same length as rows & columns
      start_grid.Length0 == target_rows_sum.Length && start_grid.Length1 == target_columns_sum.Length &&
      player_grid.Length0 == target_rows_sum.Length && player_grid.Length1 == target_columns_sum.Length
    }

    constructor(size: int)
      requires size > 0
      ensures Valid()
    {
      start_grid := new int[size, size]((i, j) => 0);
      target_grid := new int[size, size]((i, j) => 0);
      target_rows_sum := new int[size](i => 0);
      target_columns_sum := new int[size](i => 0);

      player_grid := new int[size, size]((i, j) => 0);
      player_rows_sum := new int[size](i => 0);
      player_columns_sum := new int[size](i => 0);
    }

    method setupGame()
      modifies this, start_grid, target_grid, target_rows_sum, target_columns_sum
      requires Valid()
      ensures Valid()
    {
      var i, j := 0, 0;
      var size := start_grid.Length0;

      while i < size
        invariant size == start_grid.Length0
        invariant Valid()
        modifies start_grid, target_grid
      {
        while j < size
          invariant size == start_grid.Length0
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
    }

    /**
    Random number generator.
    */
    method random() returns (randomNumber: nat)
      ensures 1 <= randomNumber <= 9
    {
      var numberSet := {1, 2, 3, 4, 5, 6, 7, 8, 9};
      randomNumber :| randomNumber in numberSet;
    }

    /**
    Random boolean generator.
    */
    method randomBool() returns (randomBool: bool)
    {
      var bools: set<bool> := {true, false};
      randomBool :| randomBool in bools;
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
