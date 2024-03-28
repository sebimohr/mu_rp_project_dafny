// C# implementation of a random number generator
using System;
using System.Numerics;

public class ExternalMethods {
    public static BigInteger RandomInt(BigInteger min, BigInteger max) {
        var random = new Random();
        return random.Next((int) min, ((int) max) + 1);
    }

    public static (BigInteger, BigInteger) ReadUserInput(BigInteger size) {
        while (true) {
            Console.WriteLine("Enter the field you want to change (Format: '#,#'): ");
            var input = Console.ReadLine();
            var numbers = input.Split(',');
            if (numbers.Length != 2) {
                Console.WriteLine("Please enter a valid combination (Format: '#,#')!");
                continue;
            }

            try {
                var row = Int32.Parse(numbers[0]);
                var column = Int32.Parse(numbers[1]);
            }
            catch (Exception e) {
                Console.WriteLine("Please enter valid numbers (Format: '#,#')!");
                continue;
            }

            if (0 <= row && row < size && 0 <= column && column < size) {
                return (row, column);
            }

            Console.WriteLine("Please enter a valid position (Format: '#,#')!");
        }
    }

    public static void PrintGrid(BigInteger[,] grid1,
                                 BigInteger[,] grid2,
                                 BigInteger[] rowSums1,
                                 BigInteger[] colSums1,
                                 BigInteger[] rowSums2,
                                 BigInteger[] colSums2)
    {
        // Clear console before rewriting
        Console.Clear();

        int rows = grid1.GetLength(0);
        int cols = grid1.GetLength(1);

        // Print column indexes
        Console.Write("    ");
        for (int j = 0; j < cols; j++)
        {
            Console.Write($" {j} ");
        }
        Console.WriteLine();

        // Print separator line
        Console.Write("   -");
        for (int j = 0; j < cols; j++)
        {
            Console.Write("---");
        }
        Console.WriteLine();

        // Print rows with indexes and row sums
        for (int i = 0; i < rows; i++)
        {
            Console.Write($"{i} | ");
            for (int j = 0; j < cols; j++)
            {
                string indicator = grid1[i, j] == grid2[i, j] ? "*" : " ";
                Console.Write($"{grid1[i, j]}{indicator} ");
            }
            Console.WriteLine($"| {rowSums1[i]}");
        }

        // Print separator line
        Console.Write("   -");
        for (int j = 0; j < cols; j++)
        {
            Console.Write("---");
        }
        Console.WriteLine();

        // Print column sums
        Console.Write("    ");
        for (int j = 0; j < cols; j++)
        {
            Console.Write($" {colSums1[j]} ");
        }
        Console.WriteLine();
    }
}
