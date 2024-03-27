// C# implementation of a random number generator
using System;
using System.Numerics;

public class ExternalMethods {
    public static BigInteger RandomInt(BigInteger min, BigInteger max) {
        var random = new Random();
        return random.Next((int) min, ((int) max) + 1);
    }
}
