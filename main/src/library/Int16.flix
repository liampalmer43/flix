/*
 * Copyright 2016 Liam Palmer
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

namespace Int16 {

    ///
    /// Returns the number of bits used to represent an `Int16`.
    ///
    def size: Int32 = 16

    ///
    /// Returns the minimum number representable by an `Int16`.
    ///
    def minValue: Int16 = 1i16 <<< (size() - 1)

    ///
    /// Returns the maximum number representable by an `Int16`.
    ///
    def maxValue: Int16 = ~~~minValue()

    ///
    /// Returns the smaller of `x` and `y`.
    ///
    def min(x: Int16, y: Int16): Int16 = if (x <= y) x else y

    ///
    /// Returns the larger of `x` and `y`.
    ///
    def max(x: Int16, y: Int16): Int16 = if (x >= y) x else y

    ///
    /// Returns the absolute value of `x`.
    /// If the absolute value exceeds maxValue(), -1 is returned.
    ///
    def abs(x: Int16): Int16 = switch {
        case x >= 0i16          => x
        case x == minValue()    => -1i16
        case x != minValue()    => -x
    }

    ///
    /// Returns the distance between `x` and `y`.
    /// If this distance exceeds maxValue(), -1 is returned.
    ///
    def dist(x: Int16, y: Int16): Int16 = switch {
        case x >= 0i16 && y >= 0i16                 => abs(x - y)
        case x < 0i16 && y < 0i16                   => abs(x - y)
        case x == minValue() || y == minValue()     => -1i16
        case minValue() + abs(x) + abs(y) >= 0i16   => -1i16
        case minValue() + abs(x) + abs(y) < 0i16    => abs(x - y)
    }

    ///
    /// Returns 1 if x > y, -1 if x < y, and 0 if x = y.
    /// The sign of x - y.
    ///
    def compare(x: Int16, y: Int16): Int32 = switch {
        case x == y  => 0
        case x < y   => -1
        case x > y   => 1
    }

    ///
    /// Returns 1 if x > 0, -1 if x < 0, and 0 if x = 0.
    /// The sign of x.
    ///
    def signum(x: Int16): Int32 = compare(x, 0i16)

    ///
    /// Returns the logical right shift of `x` by `distance`.
    /// Only the rightmost 5 bits of `distance` are considered (ie. `distance % 32`).
    /// A zero is shifted into the leftmost position regardless of sign extension.
    ///
    def logicalRightShift(x: Int16, distance: Int32): Int16 =
        if (x < 0i16 && distance % 32 != 0)
            ((x >>> 1) &&& maxValue()) >>> (distance - 1)
        else
            x >>> distance

    ///
    /// Returns the number of one-bits in the two's complement binary
    /// representation of `x`.
    ///
    def bitCount(x: Int16): Int32 = switch {
        case x == 0i16        => 0
        case x % 2i16 != 0i16 => bitCount(logicalRightShift(x, 1)) + 1
        case x % 2i16 == 0i16 => bitCount(logicalRightShift(x, 1))
    }

    ///
    /// Returns the the value obtained by rotating the two's complement
    /// binary representation of `x` right by `distance` bits.
    ///
    def rotateRight(x: Int16, distance: Int32): Int16 =
        let rem = distance % size();
        let rot = if (rem >= 0) rem else rem + size();
        (logicalRightShift(x, rot)) ||| (x <<< (size() - rot))

    ///
    /// Returns the the value obtained by rotating the two's complement
    /// binary representation of `x` left by `distance` bits.
    ///
    def rotateLeft(x: Int16, distance: Int32): Int16 =
        let rem = distance % size();
        let rot = if (rem >= 0) rem else rem + size();
        (logicalRightShift(x, size() - rot)) ||| (x <<< rot)

    ///
    /// Returns the value obtained by reversing the bits in the
    /// two's complement binary representation of `x`.
    ///
    def reverse(x: Int16): Int16 = reverseHelper(x, 0, size()-1)

    ///
    /// Helper function for `reverse`.
    ///
    @internal
    def reverseHelper(x: Int16, l: Int32, r: Int32): Int16 =
        if (l >= r) x else reverseHelper(swap(x, l, r), l+1, r-1)

    ///
    /// Helper function for `reverse`.
    ///
    @internal
    def swap(x: Int16, l: Int32, r: Int32): Int16 = match (getBit(x, l), getBit(x, r)) with {
        case (1, 0) => clearBit(setBit(x, r), l)
        case (0, 1) => clearBit(setBit(x, l), r)
        case _ => x
    }

    ///
    /// Returns the position of the highest-order/leftmost one-bit in `x`.
    /// Possible return values: 0 (rightmost bit) - 15 (leftmost bit)
    ///                         -1 if x = 0
    ///
    def highestOneBitPosition(x: Int16): Int32 =
        // Start at bit 15 and scan right
        oneBitPositionHelper(x, size() - 1, -1)

    ///
    /// Returns the position of the lowest-order/rightmost one-bit in `x`.
    /// Possible return values: 0 (rightmost bit) - 15 (leftmost bit)
    ///                         -1 if x = 0
    ///
    def lowestOneBitPosition(x: Int16): Int32 =
        // Start at bit 0 and scan left
        oneBitPositionHelper(x, 0, 1)

    ///
    /// Helper function for highestOneBitPosition and lowestOneBitPosition.
    /// If `x` has a one-bit at `position`, return that position.
    /// Otherwise recursively check the next bit in the same way.
    ///
    @internal
    def oneBitPositionHelper(x: Int16, position: Int32, delta: Int32): Int32 = switch {
        case position < 0                   => -1
        case position > (size() - 1)        => -1
        case getBit(x, position) == 1          => position
        case delta == 0                     => -1
        case getBit(x, position) == 0          => oneBitPositionHelper(x, position + delta, delta)
    }

    ///
    /// Returns a value with at most a single one-bit, in the position
    /// of the highest-order/leftmost one-bit in `x`.
    /// Returns 0 if x=0.
    ///
    def highestOneBit(x: Int16): Int16 =
        bitPositionToInt(highestOneBitPosition(x))

    ///
    /// Returns a value with at most a single one-bit, in the position
    /// of the highest-order/leftmost one-bit in `x`.
    /// Returns 0 if x=0.
    ///
    def lowestOneBit(x: Int16): Int16 =
        bitPositionToInt(lowestOneBitPosition(x))

    ///
    /// Helper function for highestOneBit and lowestOneBit.
    /// Returns a value with a single one-bit at bit number `position`.
    /// Returns 0 if `position` is outside the range 0-15 inclusive.
    ///
    @internal
    def bitPositionToInt(position: Int32): Int16 =
        if (position < 0 || position > size() - 1) 0i16 else 1i16 <<< position

    ///
    /// Returns the number of zero bits preceding the
    /// highest-order/leftmost one-bit in `x`.
    /// Returns 16 if x=0.
    ///
    def numberOfLeadingZeros(x: Int16): Int32 =
        if (x == 0i16) size() else size() - 1 - highestOneBitPosition(x)

    ///
    /// Returns the number of zero bits following the
    /// lowest-order/rightmost one-bit in `x`.
    /// Returns 16 if x=0.
    ///
    def numberOfTrailingZeros(x: Int16): Int32 =
        if (x == 0i16) size() else lowestOneBitPosition(x)

    ///
    /// Returns the bit of `x` at `position` (either 0 or 1).
    /// Considers the 5 rightmost bits of `position` (`position` mod 32).
    /// The bits of x have positions: 0 (rightmost bit) - 15 (leftmost bit)
    ///
    def getBit(x: Int16, position: Int32): Int32 =
        if ((x >>> position) % 2i16 == 0i16) 0 else 1

    ///
    /// Returns `x` with the bit at position `position` set (to 1).
    /// Considers the 5 rightmost bits of `position` (`position` mod 32).
    /// The bits of x have positions: 0 (rightmost bit) - 15 (leftmost bit)
    ///
    def setBit(x: Int16, position: Int32): Int16 = x ||| (1i16 <<< position)

    ///
    /// Returns `x` with the bit at position `position` cleared (to 0).
    /// Considers the 5 rightmost bits of `position` (`position` mod 32).
    /// The bits of x have positions: 0 (rightmost bit) - 15 (leftmost bit)
    ///
    def clearBit(x: Int16, position: Int32): Int16 = x &&& ~~~(1i16 <<< position)

    ///
    /// Returns `x` with the bit at position `position` flipped.
    /// Considers the 5 rightmost bits of `position` (`position` mod 32).
    /// The bits of x have positions: 0 (rightmost bit) - 15 (leftmost bit)
    ///
    def flipBit(x: Int16, position: Int32): Int16 = x ^^^ (1i16 <<< position)
}
