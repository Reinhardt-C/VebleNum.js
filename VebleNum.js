let O = VebleNum = function(input) { return new Ordinal(input) }; // Shorthand function

class Ordinal {
    constructor(input) {
        if (input == undefined) this.value = 0; // Handle people being stupid
        else if (typeof input == 'number') this.value = input; // Handle integer input
        else if (typeof input == 'string') this.value = fromString(input).value; // Handle string input
        else if (input instanceof Array) this.value = JSON.parse(JSON.stringify(input)); // Handle TAN input
        else if (input.value !== undefined) this.value = new Ordinal(input.value).value; // Hanle object input
        else this.value = 0; // Failsafe

        this.normalize(); // Don't stuff up
    }

    get isLim() { // Tests if an ordinal is a limit
        if (!(this.value instanceof Array)) return this.value == 0; // The only finite limit ordinal is 0
        return new Ordinal(this.value[0]).isLim; // If the added part is 0, then above, otherwise go down until either not 0 or 0
    }

    get isSucc() {
        return !this.isLim; // The opposite of the above getter
    }

    get isFinite() {
        return typeof this.value == 'number'; // Return if the ordinal is finite or not
    }
    
    get isTransfinite() {
        return typeof this.value != 'number'; // Return if the ordinal is infinite or not
    }

    get isGamma() { // Additively indecomposable
        if (this.isFinite) {
            if (this.value == 1) return true; // 1 is the only finite additively indecomposable ordinal
            return false;
        }
        if (this.eq([0])) return true; // w is additively indecomposable
        if (this.value.length < 2) return false; // w+n for n!=0 is not additively indecomposable
        return this.value[0] === 0; // If you're adding something then it's obviously not additively indecomposable
    }

    get isDelta() { // Multiplicatively indecomposable
        if (this.isFinite) {
            if (this.value == 2) return true; // 2 is the only finite multiplicatively indecomposable ordinal
            return false;
        }
        if (this.eq([0])) return true; // w is multiplicatively indecomposable
        if (this.value.length < 2) return false; // w+n for n!=0 isn't multiplicatively indecomposable
        return this.isEpsilon || new Ordinal(this.value[1]).isGamma; // Epsilon numbers are multiplicatively indecomposable, and the other cases are if it's w^(any additively indecomposable ordinal)
    }

    get isEpsilon() { // Exponentially indecomposable
        if (this.isFinite) return false; // No finite numbers are exponentially indecomposable
        if (this.value.length < 3) return false; // No ordinals < e0 are exponentially indecomposable
        return !(this.value[0] !== 0 || this.value[1] !== 0); // a+n and a*w^n for n!=0 are not exponentially indecomposable
    }

    get isZeta() {
        if (this.isFinite) return false; // Pretty much all the same, but epilon-y indecomposable?
        if (this.value.length < 4) return false;
        return !(this.value[0] !== 0 || this.value[1] !== 0 || this.value[2] !== 0);
    }

    get isEta() {
        if (this.isFinite) return false; // Pretty much all the same, but zeta-y indecomposable?
        if (this.value.length < 4) return false;
        return !(this.value[0] !== 0 || this.value[1] !== 0 || this.value[2] !== 0 || this.value[3] !== 0);
    }

    isPhi(n) { // Pretty much all the same, but phi(n-1)-y indecomposable?
        if (n == 0) return this.isGamma;
        if (n == 1) return this.isEpsilon;
        if (n == 2) return this.isZeta;
        if (n == 3) return this.isEta;
        if (this.value.length < n + 1) return false;
        for (let i = 0; i < n + 1; i++) if (this.value[i] !== 0) return false;
        return true;
    }

    fundSequence(el) { // Get the el'th element of one of the ordinals fundamental sequences (a[n] for a being this ordinal)
        if (this.isSucc || this.value === 0) return undefined; // Successors and 0 have no fundamental sequence as their cofinality is 0
        if (this.value[0] !== 0) { // a+b for limit b has a fundamental sequence comprised of a+b[n]
            let x = new Ordinal(this.value[0]).fundSequence(el);
            let y = [...this.value];
            y[0] = x.value;
            return new Ordinal(y);
        }
        if (this.value.length == 1 && this.value[0] == 0) return new Ordinal(el); // Fundamental sequence for w is 0, 1, 2, 3...
        let o = new Ordinal(this); // Don't override this ordinal
        let x; 
        for (let i in this.value) { // Here we take the fundamental sequence of the least significant part
            x = i;
            if (this.value[i] !== 0) break;
        }
        let n = new Ordinal(this.value[x]); // Get the part we found in the above step
        if (n.isSucc) { // Handle gross successor ordinals
            let y = x - 1;
            if (typeof o.value[x] == 'number') {
                o.value[x]--
            } else {
                o.value[x][0]--;
            }
            for (let i = 0; i < el; i++) {
                let a = [...o.value];
                o.value[y] = a;
            }
            o.normalize();
            return o;
        }
        let w = new Ordinal(this.value[x]).fundSequence(el); // Get the fundamental sequence of the part we found above
        let v = [...this.value]; // Don't override this ordinal
        v[x] = w.value; // Apply to the original part
        return new Ordinal(v); // We done
    }

    cmp(other) { // Comparing two ordinals
        this.normalize(); // Don't stuff up
        other = new Ordinal(other); // ^
        if (this.value instanceof Array && !(other.value instanceof Array)) return 1; // Infinite > finite
        if (other.value instanceof Array && !(this.value instanceof Array)) return -1; // Finite < infinite
        if (!(this.value instanceof Array) && !(other.value instanceof Array)) return (this.value == other.value ? 0 : (this.value > other.value ? 1 : -1)); // Compare smol numbers
        if (this.value.length > other.value.length) return 1; // w^2 > w, e0 > w^2, z0 > e0 etc.
        if (this.value.length < other.value.length) return -1; // w^2 > w, e0 > w^2, z0 > e0 etc.
        for (let i = this.value.length - 1; i >= 0; i--) { // Run through the components, most significant to least
            let x = new Ordinal(this.value[i]); // To compare we need an ordinal
            let z = x.cmp(other.value[i]); // Compare the components
            if (z != 0) return z; // If they're not equal then tell us the result
        }
        return 0; // We tried everything, they must be equal
    }

    eq(other) { return this.cmp(other) === 0; } // Are they equal?
    neq(other) { return this.cmp(other) !== 0; } // Are they not equal?
    gt(other) { return this.cmp(other) > 0; } // Is this one bigger?
    gte(other) { return this.cmp(other) > -1; } // Is this one bigger or equal?
    lt(other) { return this.cmp(other) < 0; } // Is this one smaller?
    gt(other) { return this.cmp(other) < 1; } // Is this one smaller or equal?

    // From this point on I barely understand what's going on, crazy ideas that seem to work and bs that probably shouldn't...

    cmpLims(other) { // For addition
        this.normalize();
        other = new Ordinal(other);
        if (this.value instanceof Array && !(other.value instanceof Array)) return 1;
        if (other.value instanceof Array && !(this.value instanceof Array)) return -1;
        if (!(this.value instanceof Array) && !(other.value instanceof Array)) return 0;
        if (this.value.length > other.value.length) return 1;
        if (this.value.length < other.value.length) return -1;
        for (let i = this.value.length - 1; i >= 1; i--) {
            let x = new Ordinal(this.value[i]).cmp(other.value[i]);
            if (x != 0) return x;
        }
        return 0;
    }

    cmpLims2(other) { // For multiplication
        this.normalize();
        other = new Ordinal(other);
        if (this.value instanceof Array && !(other.value instanceof Array)) return 1;
        if (other.value instanceof Array && !(this.value instanceof Array)) return -1;
        if (!(this.value instanceof Array) && !(other.value instanceof Array)) return 0;
        if (this.value.length < 3 && other.value.length < 3) return 0;
        if (this.value.length >= 2 && this.value.length > other.value.length) return 1;
        if (other.value.length >= 2 && this.value.length < other.value.length) return -1;
        for (let i = this.value.length - 1; i >= 2; i--) {
            let x = new Ordinal(this.value[i]).cmp(other.value[i]);
            if (x != 0) return x;
        }
        return 0;
    }

    condense(other) { // For addition
        let x = new Ordinal(this);
        other = new Ordinal(other);
        if (x.cmpLims(other) == -1) {
            x = new Ordinal(0);
        } else if (typeof x.value == 'number') {
            return x;
        } else {
            x.value[0] = new Ordinal(x.value[0]).condense(other).value;
        }
        return x;
    }

    condense2(other,first = true) { // For multiplication
        let x = new Ordinal(this);
        other = new Ordinal(other);
        if (first && x.cmpLims2(other) < 0 || !first && x.cmpLims2(other) < 1) {
            x = new Ordinal(0);
        } else if (typeof x.value == 'number') {
            return x;
        } else {
            x.value[0] = new Ordinal(x.value[0]).condense2(other, false).value;
        }
        return x;
    }

    add(other) {
        let x = new Ordinal(this);
        other = new Ordinal(other);
        let c = x.cmpLims(other);
        if (c == -1) return other;
        if (!(x.value instanceof Array) && !(other.value instanceof Array)) return new Ordinal(x.value + other.value);
        if (x.eq(0)) return other;
        if (other.eq(0)) return x;
        let o = x.condense(other);
        o.value[0] = new Ordinal(o.value[0]).add(other).value;
        if (getArrayDepth(o.value) > 10) return new Ordinal(NaN);
        return o;
    }

    mul(other) {
        let x = new Ordinal(this);
        other = new Ordinal(other);
        if (!(x.value instanceof Array) && !(other.value instanceof Array)) return new Ordinal(x.value * other.value);
        if (x.eq(0) || other.eq(0)) return 0;
        if (x.eq(1)) return other;
        if (other.eq(1)) return x;
        if (this.isFinite && other.isSucc) {
            let y = new Ordinal(other.value[0]);
            let z = new Ordinal(other);
            z.value[0] = 0;
            return this.mul(z).add(this.mul(y));
        }
        let c = x.cmpLims2(other);
        if (c == -1) return other;
        if (other.value instanceof Array) {
            if (other.value[0] !== 0) {
                let y = new Ordinal(0);
                let z = new Ordinal(other);
                z.value[0] = 0;
                y = y.add(x.mul(z));
                y = y.add(x.mul(other.value[0]));
                return y;
            }
            if (x.value.length < 2) x.value[1] = 0;
            if (other.value.length < 2) other.value[1] = 0;
            else if (other.value.length > 2) {
                x.value[1] = new Ordinal(x.value[1]).add(other).value;
                return x;
            }
            other.value[1] = new Ordinal(1).add(other.value[1]).value;
            new Ordinal(x.value[0]).add(other.value[0]).value;
            x = x.condense2(other);
            x.value[1] = new Ordinal(x.value[1]).add(other.value[1]).value;
            return x;
        } else {
            if (other.value > 10) return new Ordinal(NaN);
            let y = new Ordinal(0);
            for (let i = 0; i < other.value; i++) {
                y = y.add(this);
            }
            return y;
        }
    }

    pow(other) {
        let x = new Ordinal(this);
        other = new Ordinal(other);
        if (this.isFinite && other.isFinite) return new Ordinal(x.value ** other.value);
        if (other.eq(0)) return new Ordinal(1);
        if (other.eq(1)) return x;
        if (x.eq(1)) return new Ordinal(1);
        if (x.eq(0) && other.neq(0)) return new Ordinal(0);
        if (x.eq(0)) return new Ordinal(NaN);
        if (this.isFinite && other.value[0] === 0) return other;

        if (other.isFinite && this.isLim) {
            if (other.value > 10) return new Ordinal(NaN);
            let y = new Ordinal(1);
            for (let i = 0; i < other.value; i++) {
                y = y.mul(x);
            }
            return y;
        }
        if (other.isTransfinite && other.value[0] !== 0) {
            let y = new Ordinal(other);
            y.value[0] = 0;
            return this.pow(y).mul(this.pow(other.value[0]));
        }
        if (x.value.length < 2) x.value[1] = 0;
        if (other.isEpsilon) {
            if (x.lt(other)) return other;
            if (x.isEpsilon) {
                x.value[1] = new Ordinal(x).value;
                x.value[1][1] = new Ordinal(x.value[1][1]).add(other.value).value;
                return x;
            }
            x.value[1] = new Ordinal(1).add(x.value[1]).mul(other).value;
            return x;
        }
        if (this.isEpsilon) x.value[1] = new Ordinal(1).add(x).mul(other).value;
        else x.value[1] = new Ordinal(1).add(x.value[1]).mul(other).value;
        return x;
    }

    epsilon() {
        this.normalize();
        if (this.isZeta) return this;
        if (this.lt([0, 0, 0, 1])) return new Ordinal([0, 0, new Ordinal(1).add(this).value]);
        let x = new Ordinal(this);
        while (x.value.length > 3) x.value.pop();
        x.normalize();
        let y = new Ordinal(this);
        y.value[0] = 0;
        y.value[1] = 0;
        let z;
        z = x.value;
        if (x.value.length == 1) z = x.value[0];
        else if (typeof x.value[1] == 'number' && x.value[1] != 0) z[1]--;
        y.value[2] = z;
        return y;
    }

    zeta() {
        this.normalize();
        if (this.isEta) return this;
        if (this.lt([0, 0, 0, 0, 1])) return new Ordinal([0, 0, 0, new Ordinal(1).add(this).value]);
        let x = new Ordinal(this);
        while (x.value.length > 4) x.value.pop();
        x.normalize();
        let y = new Ordinal(this);
        y.value[0] = 0;
        y.value[1] = 0;
        y.value[2] = 0;
        let z;
        z = x.value;
        if (x.value.length == 1) z = x.value[0];
        else if (typeof x.value[1] == 'number' && x.value[1] != 0) z[1]--;
        y.value[3] = z;
        return y;
    }

    eta() {
        this.normalize();
        if (this.isPhi(4)) return this;
        if (this.lt([0, 0, 0, 0, 0, 1])) return new Ordinal([0, 0, 0, 0, new Ordinal(1).add(this).value]);
        let x = new Ordinal(this);
        while (x.value.length > 5) x.value.pop();
        x.normalize();
        let y = new Ordinal(this);
        y.value[0] = 0;
        y.value[1] = 0;
        y.value[2] = 0;
        y.value[3] = 0;
        let z;
        z = x.value;
        if (x.value.length == 1) z = x.value[0];
        else if (typeof x.value[1] == 'number' && x.value[1] != 0) z[1]--;
        y.value[4] = z;
        return y;
    }

    phi(n) {
        if (n instanceof Ordinal) n = n.value;
        if (n == 0) return new Ordinal([0]).pow(this);
        if (n == 1) return this.epsilon();
        if (n == 2) return this.zeta();
        if (n == 3) return this.eta();
        this.normalize();
        if (this.isPhi(n + 1)) return new Ordinal(this);;
        let t = new Array(n + 3).fill(0);
        t[n + 2] = 1;
        let u = new Array(n + 2).fill(0);
        u[n + 1] = new Ordinal(1).add(this).value;
        if (this.lt(t)) return new Ordinal(u);
        let x = new Ordinal(this);
        while (x.value.length > n + 2) x.value.pop();
        x.normalize();
        let y = new Ordinal(this);
        for (let i = 0; i < n + 1; i++) y.value[i] = 0;
        let z;
        z = x.value;
        if (x.value.length == 1) z = x.value[0];
        else if (typeof x.value[1] == 'number' && x.value[1] != 0) z[1]--;
        y.value[n + 1] = z;
        return y;
    }

    normalize() {
        if (this.value instanceof Array) {
            if (this.value.length == 0) this.value = 0;
            else {
                if (getArrayDepth(this.value) > 10) return new Ordinal(NaN);
                while (this.value.length > 1 && this.value[this.value.length - 1] === 0) {
                    this.value.pop();
                }
                for (let i of this.value) {
                    if (i instanceof Array) {
                        let o = new Ordinal(i);
                        o.normalize();
                        i = o.value;
                    }
                }
            }
            for (let i of this.value) {
                i = new Ordinal(i).value;
                if (i.length > this.value.length) {
                    this.value = i;
                    break;
                }
            }
        }
    }

    toString() {
        this.normalize();
        if (this.isFinite) return this.value.toString();
       
        if (this.value[0] !== 0) {
            let x = new Ordinal(this);
            x.value[0] = 0;
            let strBase = x.toString();
            let strAdd = new Ordinal(this.value[0]).toString();
            let bm = 1;
            while (strAdd.startsWith(strBase)) {
                strAdd = strAdd.substring(strBase.length);
                strAdd = strAdd.replace(/^\*/, '');
                if (/\d/.test(strAdd.charAt(0))) {
                    let z = parseFloat(strAdd.match(/\d+/)[0]);
                    bm += z - 1;
                    strAdd = strAdd.substring(("" + z).length);
                }
                while (strAdd.charAt(0) == '+') {
                    strAdd = strAdd.substring(1);
                }
                bm++
            }
            if (bm == 1) return strBase + ((strAdd != '0' && strAdd != '') ? '+' + strAdd : '')
            return strBase + '*' + bm + ((strAdd != '0' && strAdd != '') ? '+' + strAdd : '')
        }
        if (this.eq([0])) return 'w';
        if (this.lt([0, 0, 1])) {
            let thing = new Ordinal(1).add(this.value[1]).toString();
            return 'w^' + (thing.length > 1 && (!(thing.search(/(w\^|e|z|n|p)/ == 0)) || thing.search(/\+/) > -1 || thing.search(/\*/) > -1) ? (`(${thing})`) : thing);
        }
        let str = '';
        for (let i = this.value.length - 1; i > 0; i--) {
            if (str == '') {
                let p = this.value.length - 2;
                let thing = new Ordinal(-1).add(this.value[i]).toString();
                let part = (thing.length > 1 && (!(thing.search(/(w\^|e|z|n|p)/ == 0)) || thing.search(/\+/) > -1 || thing.search(/\*/) > -1) ? (`(${thing})`) : thing);
                if (p == 1) str = `e${part}`;
                else if (p == 2) str = `z${part}`;
                else if (p == 3) str = `n${part}`;
                else str = `p(${p},${thing})`
            } else {
                if (this.value[i] === 0) continue;
                let p = i - 1;
                let v = this.value[i];
                let thing = O(str).add(v).toString();
                let part = (thing.length > 1 && (!(thing.search(/(w\^|e|z|n|p)/ == 0)) || thing.search(/\+/) > -1 || thing.search(/\*/) > -1) ? (`(${thing})`) : thing);
                if (p == 0) str = `w^${part}`;
                else if (p == 1) str = `e${part}`;
                else if (p == 2) str = `z${part}`;
                else if (p == 3) str = `n${part}`;
                else str = `p(${p},${thing})`
            }
        }

        return str;
    }
}

function getArrayDepth(value) {
    return Array.isArray(value) ? 
      1 + Math.max(...value.map(getArrayDepth)) :
      0;
}

function getValueAtDepth(array,depth) {
    let x = array;
    for (let i = 0; i < depth; i++) {
        x = x[0];
    }
    return x;
}

function fromString(str) {
    str = str.replace(/phi/g, 'p');
    return toAST(str).evaluate(); 
}

function toRPN(str) {
    return Parser.toRPN(Parser.tokenize(str)).map(e => e.value).join(' ');
}

function toAST(str) {
    return Parser.toAST(Parser.tokenize(str));
}

function Parser() { };

Parser.tokenize = function (str) {
    let array = [];
    let numBuff = [];
    str = str.replace(/\s+/g, '').split('');
    str.forEach(char => {
        let l = numBuff.length;
        if (Parser.isDigit(char)) numBuff.push(char);
        if (l == numBuff.length && l != 0) {
            array.push(new Token('LITERAL', numBuff.join('')));
            numBuff = [];
        }
        if (Parser.isComma(char)) array.push(new Token('SEPARATOR', char));
        if (Parser.isOperator(char)) array.push(new Token('OPERATOR', char));
        if (Parser.isFunc(char)) array.push(new Token('FUNC', char));
        if (Parser.isLeftParen(char)) array.push(new Token('LPAREN', char));
        if (Parser.isRightParen(char)) array.push(new Token('RPAREN', char));
    });
    if (numBuff.length != 0) {
        array.push(new Token('LITERAL', numBuff.join('')));
        numBuff = [];
    }
    return array;
}

Parser.toRPN = function (tokens) {
    let output = [];
    let stack = [];
    for (let token of tokens) {
        if (token.type == 'LITERAL') output.push(token);
        else if (token.type == 'FUNC') stack.push(token);
        else if (token.type == 'OPERATOR') {
            while (stack.length > 0 &&
                ((stack[stack.length - 1].type == 'FUNC')
                    || (stack[stack.length - 1].type == 'OPERATOR' && stack[stack.length - 1].prec() > token.prec())
                    || (stack[stack.length - 1].type == 'OPERATOR' && stack[stack.length - 1].prec() == token.prec() && token.assoc() == 'left')
                )
            ) output.push(stack.pop());
            stack.push(token);
        } else if (token.type == 'LPAREN') stack.push(token);
        else if (token.type == 'RPAREN') {
            while (stack.length > 0 && stack[stack.length - 1].type != 'LPAREN') output.push(stack.pop());
            if (stack.length > 0) stack.pop();
        }
    }
    while (stack.length > 0) output.push(stack.pop());
    return output;
}

Parser.toAST = function (tokens) {
    let output = [];
    let stack = [];
    for (let token of tokens) {
        if (token.type == 'LITERAL') output.push(new ASTNode(token));
        else if (token.type == 'FUNC') stack.push(token);
        else if (token.type == 'OPERATOR') {
            while (stack.length > 0 &&
                ((stack[stack.length - 1].type == 'FUNC')
                    || (stack[stack.length - 1].type == 'OPERATOR' && stack[stack.length - 1].prec() > token.prec())
                    || (stack[stack.length - 1].type == 'OPERATOR' && stack[stack.length - 1].prec() == token.prec() && token.assoc() == 'left')
                )
            ) {
                let t = stack.pop();
                output.addNode(t, t.unary() || false);
            }
            stack.push(token);
        } else if (token.type == 'LPAREN') stack.push(token);
        else if (token.type == 'RPAREN') {
            while (stack.length > 0 && stack[stack.length - 1].type != 'LPAREN') {
                let t = stack.pop();
                output.addNode(t, t.unary() || false);
            }
            if (stack.length > 0) stack.pop();
        }
    }
    while (stack.length > 0) {
        let t = stack.pop();
        output.addNode(t, t.unary() || false);
    }
    return output[0];
}

Parser.isComma = char => char == ',';
Parser.isDigit = char => /\d|w/.test(char);
Parser.isOperator = char => /\+|\*|\^/.test(char);
Parser.isFunc = char => /e|z|n|p/.test(char);
Parser.isLeftParen = char => char == '(';
Parser.isRightParen = char => char == ')';

Parser.ASSOC = {
    '+': 'left',
    '*': 'left',
    '^': 'right'
}

Parser.PREC = {
    '+': 2,
    '*': 3,
    '^': 4
}

Parser.ISUNARY = {
    'e': true,
    'z': true,
    'n': true,
    'p': false
}

function Token(type, value) {
    this.type = type;
    this.value = value;
}

Token.prototype.prec = function () { return Parser.PREC[this.value] };
Token.prototype.assoc = function () { return Parser.ASSOC[this.value] };
Token.prototype.unary = function () { return Parser.ISUNARY[this.value] || false};

function ASTNode(token, left = null, right = null) {
    this.token = token;
    this.left = left;
    this.right = right;
}

Array.prototype.addNode = function (token, unary = false) { right = this.pop(); if (!unary) left = this.pop(); else left = null; this.push(new ASTNode(token, left, right)); }

ASTNode.prototype.evaluate = function () {
    if (this.left === null && this.right === null) {
        if (this.token.value == 'w') return new Ordinal([0]);
        return new Ordinal(parseFloat(this.token.value));
    }
    let r = this.right.evaluate();
    if (this.left === null) {
        if (this.token.value == 'e') return r.epsilon();
        if (this.token.value == 'z') return r.zeta();
        if (this.token.value == 'n') return r.eta();
    }
    let l = this.left.evaluate();
    if (this.token.value == '+') return l.add(r);
    if (this.token.value == '*') return l.mul(r);
    if (this.token.value == '^') return l.pow(r);
    if (this.token.value == 'p') return O(r.value).phi(O(l.value));
}