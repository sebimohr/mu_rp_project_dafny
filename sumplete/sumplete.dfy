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
    var grid: array2<Cell>
    var sum_target: Sums
    var sum_current: Sums

    constructor(size: nat)
      requires size > 0
    {
      var cell := new Cell();
      grid := new Cell[size, size]((i, j) => cell);

      sum_target := new Sums(size);
      sum_current := new Sums(size);
    }

    method setupGame()
      modifies this
    {
      var i := 0;
      // setup numbers in every field
      // for i := 0 to grid.Length0
      while i < grid.Length0
        decreases grid.Length0 - i
      {
        assert i < grid.Length0;
        var j := 0;
        assert i < grid.Length0;

        while j < grid.Length1
          decreases grid.Length1 - j
        {
          assert i < grid.Length0;
          assert j < grid.Length1;
          // creating "random" number -> not really random though
          var randNum := random(i, j);

          // creating new cell, so it doesn't violate access modifier
          var cell := new Cell();
          cell.setNum(randNum);

          grid[i, j] := cell;

          j := j + 1;
        }

        i := i + 1;
      }
    }

    /**
    Semi random number
     */
    method random(num1: int, num2: int) returns (randomNumber: nat)
    {
      var randNumbers := new int[] [4, 17, 2, 10, 16, 6, 14, 19, 8, 1, 3, 12, 11, 3, 0, 15, 2, 18, 9, 7];
      var randNumberPos := ((num1 * num2 + 13) * 7) % randNumbers.Length;
      assert randNumberPos < randNumbers.Length;
      randomNumber := randNumbers[randNumberPos];
    }

    /**
    Gets the current sum of a row or column.
  
    index: row or column index
    isRow: declares if a row or a column should be summed up
  
    returns: The current sum of the selected row or column
     */
    method getSum(index: nat, isRow: bool) returns (sum: nat)
      requires index < grid.Length0 && index < grid.Length1
    {
      sum := 0;

      if isRow {
        for i := 0 to grid.Length1 {
          sum := sumToIfCellActive(sum, grid[index, i]);
        }
      }
      else {
        for i := 0 to grid.Length0 {
          sum := sumToIfCellActive(sum, grid[i, index]);
        }
      }
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

