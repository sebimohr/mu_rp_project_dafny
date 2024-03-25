/*
Sebastian Mohr - 23141808
Project: Part 1 - Sumplete
*/

module DataStructure {
  /**
  Sums of a grid.
   */
  class Sums {
    var rows: array<int>
    var columns: array<int>

    constructor(size: nat)
      ensures rows.Length == size
      ensures columns.Length == size
    {
      rows := new int[size];
      columns := new int[size];
    }

    method updateRows(sums: array<int>)
      modifies this
      requires sums.Length == rows.Length
    {
      rows := sums;
    }

    method updateColumns(sums: array<int>)
      modifies this
      requires sums.Length == columns.Length
    {
      columns := sums;
    }

    /*
    function rowsMatch(playerRows: array<int>) : (matches: bool)
      reads playerRows
      reads this
      requires rows.Length == playerRows.Length
      ensures forall i | 0 <= i < rows.Length :: rows[i] == playerRows[i] ==> matches == true
      ensures exists i | 0 <= i < rows.Length :: rows[i] != playerRows[i] ==> matches == false
    {
      // TODO
    }
    */
  }

  /**
  The sumplete grid.
   */
  class Grid {
    // n*n grid -> rows*columns
    var grid_start: array2<int>
    var sum_target: Sums

    var grid_player: array2<int>
    var sum_player: Sums

    constructor(grid: array2<int>)
      requires grid.Length0 == grid.Length1
      ensures grid_start.Length0 == grid_start.Length1
      ensures grid_start.Length0 == grid_player.Length0
      ensures grid_start.Length1 == grid_player.Length1
      ensures grid_start.Length0 == sum_target.rows.Length
      ensures grid_player.Length0 == sum_player.rows.Length
    {
      grid_start := grid;
      grid_player := new int[grid.Length0, grid.Length1]((i, j) => 0);

      sum_target := new Sums(grid.Length0);
      sum_player := new Sums(grid.Length0);
    }

    /**
    Sets the row or column sum.
     */
    /*
    method setSums(rowSums: array<int>, columnSums: array<int>)
      modifies this
      requires rowSums.Length == sum_target.rows.Length
      requires columnSums.Length == sum_target.columns.Length
    {
      sum_target.updateRows(rowSums);
      sum_target.updateColumns(columnSums);
    }*/
  }
}

module GameSetup {
  import dataStructure = DataStructure

  /**
  Sets up the game with a random grid of size given and sums for all rows and columns.
   */
  method setupGame(size: nat) returns (grid: dataStructure.Grid)
    requires size > 0
  {
    var newGrid := createRandomGridOfSize(size);
    grid := new dataStructure.Grid(newGrid);

    var solutionGrid := createRandomSolutionGrid(newGrid);
  }

  /**
  Creates a grid of size, with random numbers in every cell.
   */
  method createRandomGridOfSize(size: nat) returns (grid: array2<int>)
    ensures grid.Length0 == grid.Length1
  {
    grid := new int[size, size]((i, j) => 0);

    var i := 0;
    var j := 0;
    while i < grid.Length0 {
      while j < grid.Length1 {
        grid[i,j] := random();
        j := j+1;
      }
      i := i+1;
    }
  }

  /**
  Creates a grid that only includes the numbers that should be counted to the column and row sums.
   */
  method createRandomSolutionGrid(grid: array2<int>) returns (solutionGrid: array2<int>)
  {
    solutionGrid := new int[grid.Length0, grid.Length1]((i, j) => 0);
    var i := 0;
    var j := 0;
    var shouldBeCounted := false;
    while i < solutionGrid.Length0 {
      while j < solutionGrid.Length1 {
        shouldBeCounted := randomBool();
        if shouldBeCounted {
          solutionGrid[i,j] := grid[i,j];
        } else {
          solutionGrid[i,j] := 0;
        }
        j := j+1;
      }
      i := i+1;
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
