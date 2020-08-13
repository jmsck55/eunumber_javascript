
// MyEuNumber for Javascript

// #Big endian functions:
//
// Javascript has built-in Array Methods: Unshift(), Shift(), Push(), Pop(), and Map()
//
// GetVersion()
// NewEun()
// NewEunExp(num, exp, maxlength, radix)
// ToNumberArray
// ArrayEquals
// RangeArrayEquals
// Print()
// ToString()
// ToAtom()
// ToEun(double a)
//
// Borrow
// Carry
// CarryRadixOnly
// Add
// ConvertRadix
// Mult
// Negate
// Subtract
// TrimLeadingZeros
// TrimTrailingZeros
// SetRound
// GetRound
// AdjustRound
// MultExp
// AddExp
//
// ProtoMultInvExp
// IntToDigits
// ExpToAtom
// GetGuessExp
// SetCalcSpeed
// GetCalcSpeed
// MultInvExp
// DivideExp
// ConvertExp
//
// EunMult
// EunAdd
// EunNegate
// EunSubtract
// EunMultInv
// EunDivide
// EunConvert

function GetVersion() {
    return 8;
}

// Constants and variables:

var divideByZeroFlag = false;
var defaultMaxlength = 180;
var defaultRadix = 10;
// var moreAccuracy = 30;
var calculationSpeed = 5; // defaultMax / moreAccuracy

var INT_MAX = 2147483647;
var MAX_RADIX = 4096;
var INT_MAX10 = 1000000000;
var MAX_RADIX10 = 1000;

var ROUND_INF = 1; // round towards +infinity or -infinity
var ROUND_ZERO = 2; // round towards zero
// var ROUND_HALF = 3; // don't round half radix
var ROUND_POS_INF = 4; // round towards positive +infinity
var ROUND_NEG_INF = 5; // round towards negative -infinity
// var ROUND_TRUNC = 6; // truncate, don't round, do your own rounding
var ROUND_PLUS_ONE = 9; // truncate, but plus one
var ROUND_MINUS_ONE = 10; // truncate, but minus one
var ROUND_ONE_INF = 11; // truncate, but add one away from zero, towards positive and negative infinity
var ROUND_TO_NEAREST_OPTION = false; // Round to nearest whole number (Eun integer), true or false

var ROUND_DOWN = ROUND_NEG_INF; // round downward.
var ROUND_UP = ROUND_POS_INF; // round upward.

var round2 = ROUND_INF;

// constants required for division algorithm:
var overflowBy;
var LOG_ATOM_MAX = Math.log(Number.MAX_VALUE);
var LOG_ATOM_MIN = Math.log(Number.MIN_VALUE);
var multInvIter = 1000000000;
var lastIterCount = -1;

var nthRootIter = 1000000000;
var lastNthRootIter = -1;
var isImaginaryFlag = 0; // false

// Begin functions:

function ToNumberArray(arg) {
    for (i = 0 ; i < arg.length ; i++) {
        arg[i] = Number(arg[i]);
    }
    return arg;
}

function RoundTowardsZero(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
}

function IsIntegerOdd(i) {
    return i & 1 == 1; // remainder(i, 2)
}

function IsIntegerEven(i) {
    return i & 1 != 1;
}

function NewEun() {
    var ret = [ [], 0, defaultMaxlength, defaultRadix ];
    return ret;
}

function NewEunExp(num, exp, maxlength, radix) {
    var ret = [ num.slice(0), exp, maxlength, radix ];
    return ret;
}

function CopyEun(n1) {
    var ret = [ n1[0].slice(0), n1[1], n1[2], n1[3] ];
    return ret;
}

function ArrayEquals(a, b) {
    if (a === b) {
        return true;
    }
    if (a != null) {
        if (b != null) {
            if (a.length == b.length) {
                for (i = a.length - 1 ; i >= 0 ; i--) {
                    if (a[i] != b[i]) {
                        return false;
                    }
                }
                return true; // arrays are equal
            }
        }
    }
    return false;
}

function RangeArrayEquals(a, b, start, stop) {
    if (a === b) {
        return true;
    }
    if (a != null) {
        if (b != null) {
            if ((a.length >= stop) && (b.length >= stop)) {
                for (i = stop; i >= start; i--) {
                    if (a[i] != b[i]) {
                        return false;
                    }
                }
                return true; // elements in arrays are equal
            }
        }
    }
    return false;
}

function Print(a) {
// takes an "eun" data-type as described below:
// var eun_a = [ [1,2,3], 123, 100, 10];
    var indent = "  ";
    document.writeln("<pre>");
    document.writeln("[");
    document.write(indent + "[");
    document.write(a[0]);
    document.writeln("],");
    document.write(indent);
    document.write(a[1]);
    document.writeln(",");
    document.write(indent);
    document.write(a[2]);
    document.writeln(",");
    document.write(indent);
    document.writeln(a[3]);
    document.writeln("]");
    document.writeln("</pre>");
}

function ToString(a) {
    // takes an eun and turns it into a string
    var st, f, tmp, len;
    if (a[3] != 10) {
        tmp = EunConvert( a, 10, Math.ceil(Math.log10(a[3]) * a[2]) );
        a = tmp;
    }
    st = a[0].slice(0);
    len = st.length;
    if (len == 0) {
        ret = "0";
        return ret;
    }
    if (st[0] < 0) {
        f = 1;
        Negate(st);
    }
    else {
        f = 0;
    }
    st = st.join("");
    if (f == 1) {
        st = "-" + st;
    }
    f++;
    if (st.length > f) {
        st = st.slice(0, f) + "." + st.slice(f, st.length);
    }
    st += "e" + a[1];
    return st;
}

function ToAtom(a) {
    // takes an eun and turns it into a double
    var st, ret;
    st = ToString(a);
    ret = parseFloat(st);
    return ret;
}

function ToEun(a, radix, max) {
    // takes a double and turns it into an eun data-type
    var ret, isSigned, exp, f, num, tmp, st;
    st = String(a);
    if (st.length == 0) {
        return null;
    }
    isSigned = ('-' == st[0]);
    if ((isSigned == true) || ('+' == st[0])) {
        st = st.slice(1);
    }
    f = st.indexOf("e");
    if (f == -1) {
        f = st.indexOf("E");
    }
    if (f != -1) {
        tmp = st.slice(f + 1);
        exp = parseInt(tmp);
        st = st.slice(0, f);
    }
    else {
        exp = 0;
    }
    while ((st.length != 0) && (st[0] == '0')) {
        st = st.slice(1);
    }
    f = st.indexOf(".");
    if (f != -1) {
        st = st.slice(0, f) + st.slice(f + 1);
        exp += f;
    }
    else {
        exp += st.length;
    }
    exp--; // ok
    while ((st.length != 0) && (st[0] == '0')) {
        exp--;
        st = st.slice(1);
    }
    if (st.length == 0) {
        exp = 0;
    }
    num = st.split('');
    for (i = 0; i < st.length; i++) {
        num[i] = Number(num[i]);
    }
    if (isSigned == true) {
        Negate(num);
    }
    ret = [ num, exp, Math.ceil(Math.log10(radix) * max), 10 ];
    if (radix != 10) {
        ret = EunConvert(ret, radix, max);
    }
    return ret;
}

// Start of myeunumber functions:

function Borrow(sum, radix) {
    for (i = sum.length - 1 ; i >= 1 ; i--) {
        if (sum[i] < 0) {
            sum[i] += radix;
            sum[i - 1]--;
        }
    }
}

function Carry(num, radix) {
    var sum, q, r, b, i;
    sum = num.slice(0);
    i = sum.length;
    i--;
    while (i >= 0) {
        b = sum[i];
        if (b >= radix) {
            q = Math.floor( b / radix ); // integer division
            r = b % radix; // modulus, or remainder
            sum[i] = r;
            if (i == 0) {
                sum.unshift(q);
                i++;
            }
            else {
                sum[i-1] += q;
            }
        }
        i--;
    }
    return sum;
}

function CarryRadixOnly(num, radix) {
    var sum, b, i;
    sum = num.slice(0);
    i = sum.length;
    i--;
    while (i >= 0) {
        b = sum[i];
        if (b != radix) {
            break;
        }
        sum[i] = 0; // modulus, or remainder
        if (i == 0) {
            sum.unshift(1);
        }
        else {
            i--;
            sum[i-1]++;
        }
    }
    return sum;
}

function Add(n1, n2) {
    var sum, tmp, c, len;
    if (n1.length >= n2.length) {
        c = n1.length - n2.length;
        // copy n1 to sum
        sum = n1.slice(0); // copy array
        tmp = n2;
    }
    else {
        c = n2.length - n1.length;
        // copy n2 to sum
        sum = n2.slice(0); // copy array
        tmp = n1;
    }
    for (i = 0 ; i < tmp.length ; i++) {
        sum[c] += tmp[i];
        c++;
    }
    return sum;
}

// ConvertRadix() follows:

var digit;

function MultByDigitCallBack(num) {
    return num * digit;
}

function ConvertRadix(number, fromRadix, toRadix) {
// See also:
// https://www.w3schools.com/jsref/jsref_map.asp
    var target, base, tmp, ptr, f;
    target = [];
    if (number.length != 0) {
        if (number[0] < 0) {
            ptr = number.slice(0);
            Negate(ptr);
            f = true;
        }
        else {
            ptr = number;
            f = false;
        }
        base = [1];
        for (i = ptr.length - 1; i >= 0; i--) {
            digit = ptr[i];
            tmp = base.map(MultByDigitCallBack);
            target = Add(tmp, target);
            target = Carry(target, toRadix);
            digit = fromRadix;
            base = base.map(MultByDigitCallBack);
            base = Carry(base, toRadix);
        }
    }
    return target;
}

function Mult(n1, n2) {
    var sum, max, len1, len2, g, h;
    len1 = n1.length;
    len2 = n2.length;
    max = len1 + len2 - 1;
    if (max == -1) {
        return [];
    }
    sum = new Array(max);
    sum.fill(0);
    for (i = 0; i < len1; i++) {
        h = i;
        g = n1[h];
        for (j = 0; j < len2; j++) {
            sum[h] += g * n2[j];
            h++;
        }
    }
    return sum;
}

function Negate(sum) {
    for (i = 0; i < sum.length; i++) {
        sum[i] = -sum[i];
    }
}

function AbsoluteValue(sum) {
    if (sum.length) {
        if (sum[0] < 0) {
            Negate(sum);
        }
    }
}

function Subtract(sum, radix) {
    var needsNegate;
    if (sum.length) {
        needsNegate = sum[0] < 0;
        if (needsNegate) {
            Negate(sum);
        }
        sum = Carry(sum, radix);
        Borrow(sum, radix);
        if (needsNegate) {
            Negate(sum);
        }
    }
    return sum;
}

// Rounding functions:

function TrimLeadingZeros(sum) {
    var len = sum.length;
    for (i = 0 ; i < len ; i++) {
        if (sum[i] != 0) {
            if (i == 0) {
                return sum;
            }
            else {
                sum = sum.slice(i);
                return sum;
            }
        }
    }
    return [];
}

function TrimTrailingZeros(sum) {
    for (i = sum.length - 1 ; i >= 0 ; i--) {
        if (sum[i] != 0) {
            if (i == sum.length - 1) {
                return sum;
            }
            else {
                sum = sum.slice(0, i + 1);
                return sum;
            }
        }
    }
    return [];
}

function SetRound(i) {
    round2 = i;
}

function GetRound() {
    return round2;
}

function AdjustRound(n1, exp, maxlength, radix) {
    var num, oldlen, f, halfRadix, ret, roundMaxlength;
    num = n1.slice(0); // copy array
    oldlen = num.length;
    num = TrimLeadingZeros(num);
    exp += num.length - oldlen;
    
    // adjust_exponent();
    oldlen = num.length;
    // in Subtract, the first element of num cannot be a zero.
    num = Subtract(num, radix);
    // use Subtract() when there are both negative and positive numbers.
    // otherwise, you can use Carry(). (for all positive numbers)
    // num = Carry(num, radix);
    num = TrimLeadingZeros(num);
    if (num.length == 0) {
        ret = [num, 0, maxlength, radix];
        return ret;
    }
    exp += num.length - oldlen;
    
    //round2();
    roundMaxlength = ((round2 == ROUND_TO_NEAREST_OPTION) && (maxlength > exp + 1)) ? exp + 1 : maxlength;
    if (roundMaxlength <= 1) {
        roundMaxlength = 1;
        if (exp <= -1) {
            if (exp == -1) {
                num = [0, num[0]];
            }
            else {
                num = [0, 0];
            }
        }
    }
    if (num.length > roundMaxlength) {
        //if (round2 == ROUND_TRUNC) {
        //    num = num.slice(0, roundMaxlength);
        //    ret = [num, exp, maxlength, radix];
        //    return ret;
        //}
        if (round2 == ROUND_ONE_INF) {
            f = num[0];
            f = (f > 0) - (f < 0); // get the sign of the number, 1 or -1
            halfRadix = 0;
        }
        else if (round2 == ROUND_PLUS_ONE) {
            f = num[0];
            f = (f > 0);
            halfRadix = 0;
        }
        else if (round2 == ROUND_MINUS_ONE) {
            f = num[0];
            f = - (f < 0);
            halfRadix = 0;
        }
        else {
            f = num[roundMaxlength];
            halfRadix = Math.floor(radix / 2);
        }
        if (IsIntegerOdd(radix)) {
            // feature: support for odd radixes
            // normally, if radix is 5, then 0,1 Rounds down, 2,3,4 Rounds up
            // actually, 1,2 Round down, 3,4 Round up
            // because, 0.2, 0.4 Round down and 0.6, 0.8 Round up
            halfRadix++;
        }
        else {
            if (round2 == ROUND_INF) {
                halfRadix--;
            }
            else if (round2 == ROUND_POS_INF) {
                f++;
            }
            else if (round2 == ROUND_NEG_INF) {
                f--;
            }
            else if ((f == halfRadix) || (f == -halfRadix)) {
                //if (round2 == ROUND_HALF) {
                //    roundMaxlength++;
                //    num = num.slice(0, roundMaxlength);
                //    ret = [num, exp, maxlength, radix];
                //    return ret;
                //}
                if (round2 == ROUND_ZERO) {
                    f = 0;
                }
            }
        }
        num = num.slice(0, roundMaxlength);
        if (halfRadix < f) {
            num[num.length - 1]++;
            num = CarryRadixOnly(num, radix);
            exp += num.length - roundMaxlength;
        }
        else if (f < -halfRadix) {
            num[num.length - 1]--;
            Negate(num);
            num = CarryRadixOnly(num, radix);
            Negate(num);
            exp += num.length - roundMaxlength;
        }
    }
    num = TrimTrailingZeros(num);
    if (num.length == 0) {
        exp = 0;
    }
    ret = [num, exp, maxlength, radix];
    return ret;
}

function MultExp(n1, exp1, n2, exp2, max, radix) {
    var num, ret;
    num = Mult(n1, n2);
    ret = AdjustRound(num, exp1 + exp2, max, radix);
    return ret;
}

function AddExp(n1, exp1, n2, exp2, max, radix) {
    var sum, ret, size;
    size = (n1.length - exp1) - (n2.length - exp2);
    if (size < 0) {
        size = -size;
        sum = new Array(size);
        sum.fill(0);
        n1 = n1.concat(sum);
    } else if (0 < size) {
        sum = new Array(size);
        sum.fill(0);
        n2 = n2.concat(sum);
    }
    if (exp1 < exp2) {
        exp1 = exp2;
    }
    sum = Add(n1, n2);
    ret = AdjustRound(sum, exp1, max, radix);
    return ret;
}


// Division and Mult Inverse:
// https://en.wikipedia.org/wiki/Newton%27s_method#Multiplicative_inverses_of_numbers_and_power_series

function ProtoMultInvExp(n0, exp0, n1, exp1, max, radix) {
    var tmp, sum, exp2;
    // a = in0;
    // n1 = in1;
    // f(a) = a * (2 - n1 * a);
    tmp = MultExp(n0, exp0, n1, exp1, max, radix); // n1 * a
    sum = tmp[0];
    exp2 = tmp[1];
    Negate(sum);
    tmp = AddExp([2], 0, sum, exp2, max, radix); // 2 - tmp
    sum = tmp[0];
    exp2 = tmp[1];
    tmp = MultExp(n0, exp0, sum, exp2, max, radix); // a * tmp
    return tmp;
}

function IntToDigits(x, radix) {
    var sum, a;
    sum = [];
    while (x != 0) {
        a = x % radix;
        x = RoundTowardsZero(x / radix);
        sum.unshift(a);
    }
    return sum;
}

function ExpToAtom(num, exp1, maxlen, radix) {
    var p, ans, lookat, len, ele;
    if (num.length == 0) {
        return 0;
    }
    // what if exp1 is too large?
    p = Math.log(radix);
    overflowBy = exp1 - Math.floor(LOG_ATOM_MAX / p) + 2; // (+2 may need to be bigger)
    if (overflowBy > 0) {
        // overflow warning in "power()" function
        // reduce size:
        exp1 -= overflowBy;
    }
    else {
        // what if exp1 is too small?
        overflowBy = exp1 - Math.floor(LOG_ATOM_MIN / p) - 2; // (-2 may need to be bigger)
        if (overflowBy < 0) {
            exp1 -= overflowBy;
        }
        else {
            overflowBy = 0;
        }
    }
    exp1 -= maxlen;
    len = num.length;
    p = Math.pow(radix, exp1);
    ans = num[0] * p;
    for (i = 1; i < len; i++) {
        p = Math.floor(p / radix);
        ele = num[i]
        if (ele != 0) {
            lookat = ans;
            ans += ele * p;
            if (ans == lookat) {
                break;
            }
        }
    }
    // if overflowBy is positive, then there was an overflow
    // overflowBy is an offset of that overflow in the given radix
    return ans;
}

function GetGuessExp(den, exp1, protoMax, radix) {
    var guess, tmp, denom, one, len, ans, sigDigits;
    sigDigits = Math.ceil(15 / Math.log10(radix));
    if (protoMax < sigDigits) {
        sigDigits = protoMax;
    }
    len = den.length;
    denom = ExpToAtom(den, len - 1, sigDigits, radix);
    one = Math.pow(radix, len - 1 - overflowBy);
    ans = RoundTowardsZero(one / denom);
    guess = IntToDigits(ans, radix); // works on negative numbers
    tmp = AdjustRound(guess, exp1, sigDigits - 1, radix);
    tmp[2] = protoMax;
    return tmp;
}

function SetCalcSpeed(a) {
    calculationSpeed = a;
}

function GetCalcSpeed() {
    return calculationSpeed;
}

function MultInvExp(den1, exp1, max, radix) {
    var guess, tmp, lookat, exp0, protoMax, len, lastLen, moreAccuracy;
    if (den1.length == 0) {
        divideByZeroFlag = true;
        return null;
    }
    if (den1.length == 1) {
        if ((den1[0] == 1) || (den1[0] == -1)) {
            lastIterCount = 1;
            return [ den1, -exp1, max, radix ];
        }
    }
    moreAccuracy = Math.ceil(max / calculationSpeed);
    protoMax = max + moreAccuracy;
    // max += 2;
    exp0 = -exp1; // negate exp1
    exp0--;
    tmp = GetGuessExp(den1, exp0, protoMax, radix);
    guess = tmp[0];
    lastLen = guess.length;
    lastIterCount = multInvIter;
    for (i = 1; i <= multInvIter; i++) {
        lookat = tmp;
        tmp = ProtoMultInvExp(guess, exp0, den1, exp1, protoMax, radix);
        guess = tmp[0];
        exp0 = tmp[1];
        len = guess.length;
        //if (len > max) {
        //    len = max;
        //}
        if (len == lastLen) {
            if (exp0 == lookat[1]) {
                if (RangeArrayEquals(guess, lookat[0], 0, len - 1)) {
                    lastIterCount = i;
                    break;
                }
            }
        }
        lastLen = len
    }
    // max -= 2
    tmp = AdjustRound(guess, exp0, max, radix);
    return tmp;
}

function DivideExp(num1, exp1, den2, exp2, max, radix) {
    var tmp;
    tmp = MultInvExp(den2, exp2, max, radix);
    tmp = MultExp(num1, exp1, tmp[0], tmp[1], max, radix);
    return tmp;
}

function ConvertExp(n1, exp1, max, fromRadix, toRadix) {
    var n2, n3, result, exp2, exp3, len, local, p1;
    if (n1.length <= exp1) {
        local = new Array(exp1 - n1.length + 1);
        local.fill(0);
        local = n1.concat(local);
        p1 = local;
    }
    else {
        p1 = n1;
    }
    n2 = ConvertRadix(p1, fromRadix, toRadix);
    exp2 = n2.length - 1;
    len = p1.length;
    //local = null;
    local = new Array(len - exp1);
    local.fill(0);
    local[0] = 1;
    n3 = ConvertRadix(local, fromRadix, toRadix);
    exp3 = n3.length - 1;
    result = DivideExp(n2, exp2, n3, exp3, max, toRadix);
    return result;
}

// eun functions:

function RemoveLastDigits(n1, digits) {
    for (i = 0 ; i < digits ; i++) {
        n1[0].pop();
    }
}

function EunMult(n1, n2) {
    var maxlength;
    if (n1[3] != n2[3]) {
        return null;
    }
    if (n1[2] >= n2[2]) {
        maxlength = n1[2];
    }
    else {
        maxlength = n2[2];
    }
    return MultExp(n1[0], n1[1], n2[0], n2[1], maxlength, n1[3]);
}

function EunAdd(n1, n2) {
    var maxlength;
    if (n1[3] != n2[3]) {
        return null;
    }
    if (n1[2] >= n2[2]) {
        maxlength = n1[2];
    }
    else {
        maxlength = n2[2];
    }
    return AddExp(n1[0], n1[1], n2[0], n2[1], maxlength, n1[3]);
}

function EunNegate(n1) {
    var ret = CopyEun(n1);
    Negate(ret[0]);
    return ret;
}

function EunSubtract(n1, n2) {
    var ret;
    ret = EunAdd(n1, EunNegate(n2));
    return ret;
}

function EunMultInv(n1) {
    var ret;
    ret = MultInvExp(n1[0], n1[1], n1[2], n1[3]);
    return ret;
}

function EunDivide(n1, n2) {
    var maxlength;
    if (n1[3] != n2[3]) {
        return null;
    }
    if (n1[2] >= n2[2]) {
        maxlength = n1[2];
    }
    else {
        maxlength = n2[2];
    }
    return DivideExp(n1[0], n1[1], n2[0], n2[1], maxlength, n1[3]);
}

function EunConvert(n1, toRadix, max) {
    var ret;
    ret = ConvertExp(n1[0], n1[1], max, n1[3], toRadix);
    return ret;
}

// Added functions:

// end of file.
