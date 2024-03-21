/*
Sebastian Mohr - 23141808
Project: Part 1 - Sumplete
*/

module DataStructure {
  class Cell {
    var num: nat
    var status: bool

    constructor() {
      num := 0;
      status := false;
    }

    method setNum(newNum: nat)
      modifies this
    {
      num := newNum;
    }

    method toggleStatus()
      modifies this
    {
      status := !status;
    }
  }

  class Sums {
    var rows: array<int>
    var columns: array<int>

    constructor(size: nat) {
      rows := new int[size];
      columns := new int[size];
    }
  }

  class Grid {
    // n*n grid -> rows*columns
    var grid_start: array2<int>
    var grid_player: array2<int>

    var sum_target: Sums
    var sum_current: Sums

    constructor(size: nat)
      requires size > 0
    {
      grid_start := new int[size, size]((i, j) => 0);
      grid_player := new int[size, size]((i, j) => 0);

      sum_target := new Sums(size);
      sum_current := new Sums(size);
    }
  }

  /**
  Sums up the cell value to the sum, but only if the cell is currently active.

  sum: Initial column or row sum
  cell: Cell that should be additioned

  returns: sum + cell.num when cell is activated, else sum
   */
  function sumToIfCellActive(sum: nat, cell: Cell): nat
    reads cell
  {
    if cell.status then sum + cell.num else sum
  }
}

module GameSetup {
  method setupRandomGrid(randomSeed: nat, grid: array2<int>)
    modifies grid
    requires grid.Length0 == grid.Length1
  {
    var i := 0;

    while i < grid.Length0
      decreases grid.Length0 - i
    {
      var j := 0;

      while j < grid.Length1
        decreases grid.Length1 - j
        invariant i < grid.Length0
      {
        grid[i,j] := random(randomSeed, i);
        j := j + 1;
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
