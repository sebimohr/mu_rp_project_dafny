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

  class Grid {
    // n*n grid -> rows*columns
    var grid: array2<Cell>

    constructor(size: nat)
      requires size > 0
    {
      var cell := new Cell();
      grid := new Cell[size, size]((i, j) => cell);
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
