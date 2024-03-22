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
  }

  /**
  The sumplete grid.
   */
  class Grid {
    // n*n grid -> rows*columns
    var grid_start: array2<int>
    var grid_player: array2<int>

    var sum_target: Sums
    var sum_current: Sums

    constructor(grid: array2<int>)
      requires grid.Length0 == grid.Length1
      ensures grid_start.Length0 == grid_start.Length1
      ensures grid_start.Length0 == grid_player.Length0
      ensures grid_start.Length1 == grid_player.Length1
      ensures grid_start.Length0 == sum_target.rows.Length
      ensures grid_player.Length0 == sum_current.rows.Length
      // ensures forall i, j :: 0 <= i < grid_start.Length0 && 0 <= j < grid_start.Length1 ==> grid_start[i,j] == 0
    {
      grid_start := grid;
      grid_player := new int[grid.Length0, grid.Length1]((i, j) => 0);

      sum_target := new Sums(grid.Length0);
      sum_current := new Sums(grid.Length0);
    }
  }
}

module GameSetup {
  import dataStructure = DataStructure

  method setupGame(randomSeed: nat, size: nat) returns (grid: dataStructure.Grid)
    requires size > 0
  {
    var randomNumber := random(randomSeed, size);
    var newGrid := new int[size, size]((i, j) => (i * j * randomNumber) % 9);
    grid := new dataStructure.Grid(newGrid);
  }

  /**
  Semi random number
   */
  method random(randomSeed: nat, num: nat) returns (randomNumber: nat)
    ensures 0 <= randomNumber <= 9
  {
    var randNumbers := new int[] [8, 3, 1, 5, 4, 2, 9, 6, 7, 0];
    var randNumberPos := ((randomSeed * num + 13) * 7) % randNumbers.Length;
    assert randNumberPos < randNumbers.Length;
    randomNumber := randNumbers[randNumberPos];
  }
}
