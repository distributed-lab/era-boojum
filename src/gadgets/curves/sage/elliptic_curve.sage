class InternalEllipticCurve:
    """
    Class for storing information about elliptic curve used
    """
    
    def __init__(self, F, a: GF, b: GF) -> None:
        """
        Initializes the elliptic curve

        Args:
            F (GF): Finite field
            a (GF): Coefficient a
            b (GF): Coefficient b
        """

        self.F = F
        self.a = a
        self.b = b

    def __str__(self) -> str:
        """
        Returns the string representation of the elliptic curve

        Returns:
            str: String representation of the elliptic curve
        """

        return f"y^2 = x^3 + {self.a}x + {self.b} over {self.F}"

    def is_on_curve(self, x: GF, y: GF) -> bool:
        """
        Checks if the point (x, y) is on the curve

        Args:
            x (GF): x-coordinate
            y (GF): y-coordinate

        Returns:
            bool: True if the point is on the curve, False otherwise
        """

        return y**2 == x**3 + self.a*x + self.b
    