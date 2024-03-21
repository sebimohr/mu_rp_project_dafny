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

    constructor(size: nat) {
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

    constructor(size: nat)
      requires size > 0
      ensures grid_start == grid_player
      ensures grid_start.Length0 == grid_start.Length1
      ensures forall i, j :: 0 <= i < grid_start.Length0 && 0 <= j < grid_start.Length1 ==> grid_start[i,j] == 0
    {
      grid_start := new int[size, size]((i, j) => 0);
      grid_player := grid_start;

      sum_target := new Sums(size);
      sum_current := new Sums(size);
    }
  }
}

module GameSetup {
  import dataStructure = DataStructure

  method setupGame(randomSeed: nat, size: nat) returns (grid: dataStructure.Grid)
    requires size > 0
  {
    grid := new dataStructure.Grid(size);
    assert forall i, j :: 0 <= i < grid.grid_start.Length0 && 0 <= j < grid.grid_start.Length1 ==> grid.grid_start[i,j] == 0;
    setupRandomGrid(randomSeed, grid.grid_start);
  }

  /**
  Sets all the fields in the grid to a semi random number, generated with the random seed
   */
  method setupRandomGrid(randomSeed: nat, grid: array2<int>)
    modifies grid
    requires grid.Length0 == grid.Length1
    requires forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 ==> grid[i,j] == 0
    ensures forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 ==> 0 <= grid[i,j] <= 9
  {
    var i := 0;

    assert forall n, m :: 0 <= n < grid.Length0 && 0 <= m < grid.Length1 ==> grid[n, m] == 0;

    while i < grid.Length0
      decreases grid.Length0 - i
      invariant 0 <= i <= grid.Length0
      invariant forall n, m :: 0 <= n < i <= grid.Length0 && 0 <= m < grid.Length1 ==> 0 <= grid[n, m] <= 9
    {
      var j := 0;

      while j < grid.Length1
        decreases grid.Length1 - j
        invariant i < grid.Length0
        invariant 0 <= j <= grid.Length1
        invariant j < grid.Length1 ==> 0 <= grid[i,j] <= 9 // TODO: Why can't this be proved on entry -> assert in l. 68
        invariant forall n, m :: 0 <= n < i <= grid.Length0 && 0 <= m < j <= grid.Length1 ==> 0 <= grid[n, m] <= 9
      {
        assert j > 0 ==> 0 <= grid[i,j-1] <= 9;

        var randomNumber := random(randomSeed, i);
        assert 0 <= randomNumber <= 9;

        grid[i,j] := randomNumber;
        assert 0 <= grid[i,j] <= 9;

        j := j + 1;
        assert 0 <= grid[i,j-1] <= 9;
      }

      i := i + 1;
    }
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
