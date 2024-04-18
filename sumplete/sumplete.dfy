/*
Sebastian Mohr - 23141808
Project: Part 1 - Sumplete
*/

include "externalMethods.cs"

/**
The sumplete grid.
 */
class Grid {
  // grid_size == n
  ghost const grid_size: int

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
    // ensuring that all variables are instantiated here so Main() is the owner
    ensures fresh(start_grid) &&
            fresh(target_grid) &&
            fresh(target_rows_sum) &&
            fresh(target_columns_sum) &&
            fresh(player_grid) &&
            fresh(player_rows_sum) &&
            fresh(player_columns_sum)
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
    modifies start_grid, target_grid, target_rows_sum, target_columns_sum
    requires Valid()
    ensures Valid()
    /**
    WHAT I WANTED TO DO HERE:
    I wanted to also ensure in the end, that all the values in the target_grid are either equal to the start_grid or 0.
     */
    // ensures forall i, j | 0 <= i < grid_size && 0 <= j < grid_size :: (start_grid[i,j] == target_grid[i,j] || target_grid[i,j] == 0)
  {
    setupGrid();
    setupSums();
  }

  method setupGrid()
    modifies this.start_grid, this.target_grid
    requires Valid()
    ensures Valid()
  {
    var i, j := 0, 0;
    var size := start_grid.Length0;

    assert forall i, j | 0 <= i < grid_size && 0 <= j < grid_size :: target_grid[i,j] == old(target_grid[i,j]);

    while i < size
      invariant size == grid_size
      invariant Valid()
      // invariant forall k, j | 0 <= k < i <= grid_size && 0 <= j < grid_size :: (target_grid[k, j] == start_grid[k, j] || target_grid[k, j] == old(target_grid[k, j]))
      // invariant forall k, j | i < k < grid_size && 0 <= j < grid_size :: target_grid[k,j] == old(target_grid[k,j])
    {
      assert i < size;
      j := 0;
      while j < size
        invariant size == grid_size
        invariant Valid()
        // invariant (0 <= i < grid_size && 0 <= j < grid_size) ==>
        //             (target_grid[i,j] == old(target_grid[i,j]) || target_grid[i,j] == start_grid[i,j])
      {
        // assert target_grid[i,j] == old(target_grid[i,j]);
        start_grid[i,j] := random();
        var randomBool := randomBool();
        if randomBool {
          target_grid[i,j] := start_grid[i,j];
        }
        j := j + 1;
      }
      i := i + 1;
    }

    // assert forall i, j | 0 <= i < grid_size && 0 <= j < grid_size :: (start_grid[i,j] == target_grid[i,j] || target_grid[i,j] == 0);
  }

  /**
  Sets up the row and column sums of the current target_grid.
   */
  method setupSums()
    modifies this.target_columns_sum, this.target_rows_sum
    requires Valid()
    ensures Valid()
  {
    var i, j := 0, 0;
    var size := start_grid.Length0;
    while i < size
      invariant size == grid_size
      invariant Valid()
      // invariant 0 <= i < grid_size ==> (forall j | 0 <= j < grid_size :: (target_grid[i,j] == 0 || target_grid[i,j] == start_grid[i,j]))
    {
      j := 0;
      while j < size
        invariant size == grid_size
        invariant Valid()
        // invariant 0 <= j < grid_size ==> (target_grid[i,j] == 0 || target_grid[i,j] == start_grid[i,j])
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
    modifies player_grid, player_rows_sum, player_columns_sum
    requires Valid()
    requires 0 <= row < grid_size && 0 <= column < grid_size
    ensures Valid()
    ensures old(player_grid[row, column]) != 0 ==> player_grid[row, column] == 0
    ensures old(player_grid[row, column]) == 0 ==> player_grid[row, column] == start_grid[row, column]
  {
    if player_grid[row, column] == 0 {
      player_grid[row, column] := start_grid[row, column];
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
    modifies player_rows_sum, player_columns_sum
    requires Valid()
    ensures Valid()
    /**
    The sums should be a sum of all elements in the rows or columns they represent.
     */
    // ensures forall i | 0 <= i < player_columns_sum.Length :: player_columns_sum[i] == GetColumnSum(player_grid, i) && player_rows_sum[i] == GetRowSum(player_grid, i)
  {
    var i, j := 0, 0;
    var size := player_grid.Length0;

    while i < size
      invariant size == grid_size
      invariant Valid()
    {
      j := 0;
      while j < size
        invariant size == grid_size
        // invariant forall m :: 0 <= m < j ==> player_rows_sum[m] == SumToRow(player_grid, i, m) && player_columns_sum[m] == SumToColumn(player_grid, j, m)
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
    ensures (forall i | 0 <= i < player_rows_sum.Length :: player_rows_sum[i] == target_rows_sum[i] && player_columns_sum[i] == target_columns_sum[i]) ==> isGameWon
    /**
    WHAT I WANTED TO DO HERE:
    The method should return false when there is at least one sum in rows or columns array that doesn't match.
     */
    // ensures (exists i | 0 <= i < player_rows_sum.Length :: player_rows_sum[i] != target_rows_sum[i] || player_columns_sum[i] != target_columns_sum[i]) ==> !isGameWon
  {
    var i := 0;
    isGameWon := true;

    while i < player_rows_sum.Length
      invariant Valid()
      invariant i <= player_rows_sum.Length
      invariant (forall j :: 0 <= j < i ==> player_rows_sum[j] == target_rows_sum[j] && player_columns_sum[j] == target_columns_sum[j]) ==> isGameWon
      // invariant (exists j :: (0 <= j < i ==> (player_rows_sum[j] != target_rows_sum[j] || player_columns_sum[j] != target_columns_sum[j]))) ==> !isGameWon
    {
      if (player_rows_sum[i] != target_rows_sum[i] || player_columns_sum[i] != target_columns_sum[i]) {
        isGameWon := false;
      }

      i := i + 1;
    }
  }

  /**
  Random number generator.

  @returns{int} Random number between 1 and 9.
  */
  method random() returns (randomNumber: int)
    ensures 1 <= randomNumber <= 9
  {
    var min := 1;
    var max := 9;
    randomNumber := RandomInt(min, max);
    expect min <= randomNumber <= max;
  }

  /**
  Random boolean generator.

  @returns{bool} Random boolean.
  */
  method randomBool() returns (randomBool: bool)
  {
    var min := 0;
    var max := 1;
    var randomNum := RandomInt(0, 1);
    expect min <= randomNum <= max;

    randomBool := randomNum == 1;
  }

  /**
  Random Int generated in a C# method.
   */
  function {:extern "ExternalMethods", "RandomInt"} RandomInt(min: int, max: int): int

  /**
  Prints the start_grid and its sums to the console.
   */
  method printToConsole()
    requires Valid()
    ensures Valid()
  {
    print "The start grid: \n";

    var i, j := 0, 0;
    while i < start_grid.Length0 {
      j := 0;
      while j < start_grid.Length1 {
        print start_grid[i, j];
        print "\t";
        j := j + 1;
      }
      print target_rows_sum[i];
      print "\n";

      j := 0;
      i := i + 1;
    }

    i := 0;
    while i < target_columns_sum.Length {
      print target_columns_sum[i];
      print "\t";
      i := i + 1;
    }
  }

  /**
  Sums up a column of a grid.

  @param{grid} The grid.
  @param{column} The column to sum up.
   */
  function GetColumnSum(grid: array2<int>, column: int): int
    requires 0 <= column < grid.Length1
    reads grid
  {
    SumToColumn(grid, column, grid.Length0)
  }

  /**
  Sums up a row of a grid.

  @param{grid} The grid.
  @param{row} The row to sum up.
   */
  function GetRowSum(grid: array2<int>, row: int): int
    requires 0 <= row < grid.Length0
    reads grid
  {
    SumToRow(grid, row, grid.Length1)
  }

  /**
  Helper: Sums up a column of a grid.

  @param{grid} The grid.
  @param{column} The column to sum up.
  @param{n} The count of numbers to be counted, should be the length of the column.
   */
  function SumToColumn(grid: array2<int>, column: int, n: int): int
    requires 0 <= column < grid.Length1
    requires 0 <= n <= grid.Length0
    reads grid
  {
    if n == 0 then 0 else SumToColumn(grid, column, n-1) + grid[n-1, column]
  }

  /**
  Helper: Sums up a row of a grid.

  @param{grid} The grid.
  @param{column} The column to sum up.
  @param{n} The count of numbers to be counted, should be the length of the column.
   */
  function SumToRow(grid: array2<int>, row: int, n: int): int
    requires 0 <= row < grid.Length0
    requires 0 <= n <= grid.Length1
    reads grid
  {
    if n == 0 then 0 else SumToRow(grid, row, n-1) + grid[row, n-1]
  }
}

method {:main} Main() {
  var grid := new Grid(3);
  grid.setupGame();
  grid.printToConsole();
}
