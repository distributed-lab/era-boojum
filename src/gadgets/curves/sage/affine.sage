from __future__ import annotations

class ExtendedAffinePoint:
    def __init__(self, x: GF, y: GF, a: GF, b: GF) -> None:
        """
        Initializes the extended short weierstrass point on elliptic curve
        E: y^2 = x^3 + ax + b

        Args:
            - (x, y) - point on E (in finite field form)
            - (a, b) - coefficients (in finite field form)
        """
        
        self._x = x
        self._y = y
        self._a = a
        self._b = b
        self._is_infty = False

    def turn_into_infinity(self) -> None:
        """
        Turn the point into infinity
        """
        self._x = 0
        self._y = 0
        self._is_infty = True
        
    def __add__(self, other: ExtendedAffinePoint) -> ExtendedAffinePoint:
        """
        Adds another ExtendedAffinePoint to the given point (basically, overiding the + operation)

        Args:
            - other - ExtendedAffinePoint, point to add
            
        Returns:
            Added point on the curve
        """
        
        if self._x != other._x:
            return self._add_unequal_x(other)

        if self._y == other._y:
            return self._double()
        
        self.turn_into_infinity()
        return self

    def _double(self) -> ExtendedAffinePoint:
        """
        Doubles the point, returning another point.
        """
        
        assert self._y != F(0)
        slope = (3*self._x*self._x + self._a) / (2*self._y)
        new_x = slope*slope - 2*self._x
        new_y = slope*(self._x - new_x) - self._y
        return ExtendedAffinePoint(new_x, new_y, self._a, self._b)
    
    def _add_unequal_x(self, other: ExtendedAffinePoint) -> ExtendedAffinePoint:
        """
        Adds another Extended Affine Point such that other.x != self.x

        Args:
            - other - ExtendedAffinePoint, point to add

        Returns:
            New point on the curve
        """
        
        assert self._x != other._x
        
        slope = (self._y - other._y) / (self._x - other._x)
        new_x = slope*slope - self._x - other._x
        new_y = slope*(self._x - new_x) - self._y
        return ExtendedAffinePoint(new_x, new_y, self._a, self._b)

    def __str__(self):
        """
        Returns the string representation of a point
        """
        return f"({self._x}, {self._y})"

a = 17
b = 6
q = 23
F = GF(23)
E = EllipticCurve(F, [17, 6])

tests = [
    ([10, 7], [7, 13]),
]

for P, Q in tests:
    print(f'We have points {P} and {Q}')
    P_E = E(P)
    Q_E = E(Q)
    R_E = P_E + Q_E
    
    P_affine = ExtendedAffinePoint(F(P[0]), F(P[1]), F(a), F(b))
    Q_affine = ExtendedAffinePoint(F(Q[0]), F(Q[1]), F(a), F(b))
    R_affine = P_affine + Q_affine

    print(f'Got: P+Q={R_affine}, expected: P+Q={R_E}')

    double_P_E = 2*P_E
    double_P_affine = P_affine + P_affine
    print(f'Got: 2*P={double_P_affine}, expected: 2*P={double_P_E}')

    double_Q_E = 2*Q_E
    double_Q_affine = Q_affine + Q_affine
    print(f'Got: 2*Q={double_Q_affine}, expected: 2*Q={double_Q_E}')