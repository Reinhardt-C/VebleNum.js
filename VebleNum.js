class VebleNum {
	constructor(input, nostandard = false) {
		if (typeof input == "string") this.value = VebleNum.fromString(input.replace(/s/g, "")).value;
		else {
			this.value = (input instanceof VebleNum ? input.value : input) || 0;
			if (!nostandard) this.standardize();
		}
	}

	standardize() {
		if (this.value instanceof Array) {
			this.value = this.value.map(e => (JSON.stringify(e) == "[0]" ? 1 : e));
			for (let i = 1; i < this.value.length; i++)
				while (
					this.value.length > 1 &&
					VebleNum.compareTerms(this.value[i], this.value[i - 1]) == 1 &&
					typeof this.value[i - 1] != "number"
				) {
					this.value.splice(i - 1, 1);
					i--;
				}
			let nums = [];
			for (let e = 0; e < this.value.length; e++) {
				let i = this.value[e];
				if (typeof i == "number") {
					nums.push(this.value.splice(e, 1)[0]);
					e--;
					continue;
				} else {
					// Handle phi(phi(1,0)) = phi(1,0), phi(phi(1,0,0),0) = phi(1,0,0) etc
					nums = [];
					for (let k in i) {
						let j = i[k];
						if (!(typeof j == "number")) {
							let t = [...i];
							t[k] = "_";
							if (typeof j.value == "number") i[k] = j.value;
							else if (j.isFixedPoint(t)) this.value[e] = j.value[0];
						}
					}
				}
				while (i.length > 1 && i[0] == 0) i.splice(0, 1);
				if (JSON.stringify(i) == "[0]") this.value[e] = 1;
			}
			let num = nums.reduce((a, b) => a + b, 0);
			if (num > 0) this.value.push(num);
			if (this.value.length == 0) this.value = 0;
			if (this.value.length == 1 && typeof this.value[0] == "number") this.value = this.value[0];
		}
	}

	add(other) {
		let o;
		if (!(other instanceof VebleNum)) o = new VebleNum(other);
		else o = other.clone();
		let res;
		if (typeof this.value == "number") {
			if (typeof o.value == "number") {
				if (o.value > 100) throw "TOO BIG OMG";
				res = new VebleNum(this.value + o.value);
			} else {
				o.value.unshift(this.value);
				res = o;
			}
		} else {
			if (typeof o.value == "number") {
				if (o.value > 100) throw "TOO BIG OMG";
				res = this.clone();
				res.value.push(o.value);
			} else {
				res = this.clone();
				res.value = res.value.concat(o.value);
			}
		}
		res.standardize();
		return res;
	}

	mul(other) {
		let o;
		if (!(other instanceof VebleNum)) o = new VebleNum(other);
		else o = other.clone();
		if (o.cmp(0) == 0) return 0;
		if (o.cmp(1) == 0) return this.clone();
		if (this.cmp(1) == 0) return o;
		let res;
		if (typeof this.value == "number") {
			if (typeof o.value == "number") {
				if (o.value > 100) throw "TOO BIG OMG";
				res = new VebleNum(this.value * o.value);
			} else if (o.value.length > 1) {
				res = new VebleNum(0);
				for (let i of o.value) {
					res = res.add(this.mul([i]));
				}
			} else res = o;
		} else {
			if (typeof o.value == "number") {
				if (o.value > 100) throw "TOO BIG OMG";
				res = this.clone();

				let c = 0;
				for (let i of res.value) if (VebleNum.compareTerms(i, res.value[0]) == 0) c++;
				let t;
				for (let i = 0; i < o.value - 1; i++) {
					t = this.clone();
					for (let j = 0; j < c; j++) res.value.splice(1, 0, t.value[0]);
				}
			} else {
				if (o.value.length > 1) {
					res = new VebleNum(0);
					for (let i of o.value) {
						res = res.add(this.mul([i]));
					}
				} else {
					res = this.clone(true);
					res.value = [res.value[0]];
					if (res.value[0].length == 1) {
						if (o.value[0].length == 1) {
							if (typeof res.value[0][0] == "number") {
								if (typeof o.value[0][0] == "number") res.value[0][0] += o.value[0][0];
								else res.value[0][0] = o.value[0][0];
							} else {
								res.value[0][0] = new VebleNum(res.value[0][0]).add(o.value[0][0]);
							}
						} else {
							res.value[0][0] = new VebleNum(res.value[0][0]).add([o.value[0]]);
						}
					} else {
						// Handle e0*w
						let t = new VebleNum([[res.clone()]], true);
						res = t.mul(o);
					}
				}
			}
		}
		res.standardize();
		return res;
	}

	pow(other) {
		let o;
		if (!(other instanceof VebleNum)) o = new VebleNum(other);
		else o = other.clone();
		if (o.cmp(0) == 0) return 1;
		if (o.cmp(1) == 0) return this.clone();
		if (this.cmp(1) == 0) return 1;
		let res;
		if (typeof this.value == "number") {
			if (typeof o.value == "number") {
				if (o.value > 100) throw "TOO BIG OMG";
				res = new VebleNum(this.value ** o.value);
			} else if (o.value.length > 1) {
				res = new VebleNum(0);
				for (let i of o.value) {
					res = res.mul(this.pow([i]));
				}
			} else {
				res = o;
			}
		} else {
			res = this.clone(true);
			if (typeof o.value == "number") {
				if (o.value > 100) throw "TOO BIG OMG";
				for (let i = 0; i < o.value - 1; i++) res = res.mul(this);
			} else {
				if (o.value.length > 1) {
					res = new VebleNum(0);
					for (let i of o.value) {
						res = res.mul(this.pow([i]));
					}
				} else {
					// phi(a,b,c...) ^ phi(d,e,f...)
					res = this.clone(true);
					res.value = [res.value[0]];
					// console.log(JSON.stringify(res), JSON.stringify(o));
					if (res.value[0].length == 1) {
						if (o.value[0].length == 1) {
							if (typeof res.value[0][0] == "number") {
								if (typeof o.value[0][0] == "number")
									res.value[0][0] = new VebleNum(res.value[0][0]).mul(o);
								else res.value[0][0] = o.value[0][0];
							} else {
								res.value[0][0] = res.value[0][0].mul(o);
							}
						} else {
							res.value[0][0] = new VebleNum(res.value[0][0]).mul(o);
						}
					} else {
						let t = new VebleNum([[res.clone()]], true);
						res = t.pow(o);
					}
				}
			}
		}
		res.standardize();
		return res;
	}

	cmp(other) {
		let o = other;
		if (!(other instanceof VebleNum)) o = new VebleNum(other);
		if (!(this.value instanceof Array)) {
			if (!(o.value instanceof Array))
				return this.value > o.value ? 1 : o.value > this.value ? -1 : 0;

			return -1;
		}
		if (this.toString() == o.toString()) return 0;
		if (!(o.value instanceof Array)) return 1;
		for (let i in this.value) {
			if (!o.value[i]) return -1;
			let t = VebleNum.compareTerms(this.value[i], o.value[i]);
			if (t == 0) continue;
			return t;
		}
	}

	isFixedPoint(a) {
		// Args like [1,0,0,'_',0] for fixed point of a -> phi(1,0,0,a,0)
		if (typeof this.value == "number") return false;
		if (this.value.length > 1) return false;
		let index = a.indexOf("_");
		for (let i = index + 1; i < a.length; i++) if (new VebleNum(a[i]).cmp(0) !== 0) return false;
		if (a.length > this.value[0].length) return false;
		if (this.value[0].length > a.length) return true;
		for (let i in a) {
			if (a[i] == "_") break;
			let cmp = new VebleNum(a[i]).cmp(this.value[0][i]);
			if (cmp == 1) return false;
			if (cmp == -1) return true;
		}
		return false;
	}

	clone(nostandard = false) {
		if (this.value instanceof Array) {
			let clone = [];
			for (let i of this.value) clone.push(VebleNum.cloneTerm(i));
			return new VebleNum(clone, nostandard);
		}
		return new VebleNum(this.value, nostandard);
	}

	toString() {
		let str = "";
		if (typeof this.value == "number") return this.value.toString();
		for (let i of this.value) {
			if (str.length > 0) str += "+";
			if (typeof i == "number") str += i;
			else {
				str += "phi(";
				str += i.toString();
				str += ")";
			}
		}
		return str;
	}

	static cloneTerm(term) {
		if (typeof term == "number") return term;
		let clone = [];
		for (let i of term) {
			if (i instanceof VebleNum) clone.push(i.clone());
			else clone.push(i);
		}
		return clone;
	}

	static compareTerms(a, b) {
		if (a == undefined || b == undefined) return 0;
		if (a instanceof VebleNum) a = a.value;
		if (b instanceof VebleNum) b = b.value;
		if (typeof a == "number") {
			if (typeof b == "number") return a > b ? 1 : a < b ? -1 : 0;
			return -1;
		}
		if (typeof b == "number") return 1;

		let maxa = VebleNum.max(...a);
		let maxb = VebleNum.max(...b);
		if (maxa.cmp([b]) == 1) return 1;
		if (maxb.cmp([a]) == -1 && new VebleNum([a]).toString() > new VebleNum([b]).toString())
			return 1;
		if (maxb.cmp([a]) == 1) return -1;
		if (maxa.cmp([b]) == -1 && new VebleNum([a]).toString() < new VebleNum([b]).toString())
			return -1;
		return 0;
	}

	static add(a, b) {
		return new VebleNum(a).add(b);
	}

	static mul(a, b) {
		return new VebleNum(a).mul(b);
	}

	static pow(a, b) {
		return new VebleNum(a).pow(b);
	}

	static max() {
		let a = [...arguments];
		let max = new VebleNum(0);
		for (let i of a) if (max.cmp(i) == -1) max = new VebleNum(i);
		return max;
	}

	static phi() {
		return new VebleNum([[...arguments]]);
	}

	static fromString(str) {
		let tokens = Parser.tokenize(str);
		let rpn = Parser.parse(tokens);
		let args = [];
		while (rpn.length > 0) {
			let token = rpn.shift();
			if (token.type == Parser.TYPES.LITERAL) {
				if (token.value == "w") args.push(new VebleNum([[1]]));
				else {
					let f = parseFloat(token.value);
					if (f > 100) throw "TOO BIG OMG";
					if (!isNaN(f)) args.push(new VebleNum(f));
					else throw "Unknown token:" + token.value;
				}
			} else if (token.type == Parser.TYPES.OPERATOR) {
				let a1 = args.pop();
				let a2 = args.pop();
				if (token.value == "+") args.push(a2.add(a1));
				else if (token.value == "*") args.push(a2.mul(a1));
				else if (token.value == "^") args.push(a2.pow(a1));
			} else if (token.type == Parser.TYPES.IDENTIFIER) {
				let a = [];
				for (let i = 0; i < token.args; i++) a.push(args.pop());
				if (token.value == "e") args.push(VebleNum.phi(1, a[0]));
				else if (token.value == "z") args.push(VebleNum.phi(2, a[0]));
				else if (token.value == "n") args.push(VebleNum.phi(3, a[0]));
				else if (token.value == "G") args.push(VebleNum.phi(1, 0, a[0]));
				else if (token.value == "phi" || token.value == "p")
					args.push(VebleNum.phi(...a.reverse()));
			}
		}
		return args[0];
	}
}

const Ordinal = VebleNum;
const O = function () {
	return new Ordinal(...arguments);
};

class Parser {
	static Token = class {
		constructor(type, value, args = 0) {
			this.type = type;
			this.value = value;
			this.args = args;
		}
	};
	static TYPES = {
		LITERAL: 0,
		IDENTIFIER: 1,
		OPERATOR: 2,
	};
	static isNumber(char) {
		return /[0-9w]/.test(char);
	}
	static isOperator(char) {
		return /[+*^(),]/.test(char);
	}
	static tokenize(str) {
		let tokens = [];
		let numbuff = [];
		let idbuff = [];
		for (let i = 0; i < str.length; i++) {
			let char = str[i];
			let type = Parser.isNumber(char) ? 0 : Parser.isOperator(char) ? 2 : 1;
			if (numbuff.length > 0 && type !== 0) {
				tokens.push(new Parser.Token(Parser.TYPES.LITERAL, numbuff.join("")));
				numbuff = [];
			}
			if (idbuff.length > 0 && type !== 1) {
				tokens.push(new Parser.Token(Parser.TYPES.IDENTIFIER, idbuff.join("")));
				idbuff = [];
			}
			if (type == 0) numbuff.push(char);
			else if (type == 1) idbuff.push(char);
			else tokens.push(new Parser.Token(Parser.TYPES.OPERATOR, char));
		}
		if (numbuff.length > 0) tokens.push(new Parser.Token(Parser.TYPES.LITERAL, numbuff.join("")));
		if (idbuff.length > 0) tokens.push(new Parser.Token(Parser.TYPES.IDENTIFIER, idbuff.join("")));
		return tokens;
	}
	static ASSOC = {
		"+": "left",
		"*": "left",
		"^": "right",
	};
	static PREC = {
		"+": 2,
		"*": 3,
		"^": 4,
	};
	static parse(tokens) {
		let output = [];
		let stack = [];
		let were_values = [];
		let arg_count = [];
		while (tokens.length > 0) {
			let token = tokens.shift();
			if (token.type == Parser.TYPES.LITERAL) {
				output.push(token);
				if (were_values.length > 0) {
					were_values.pop();
					were_values.push(true);
				}
			} else if (token.type == Parser.TYPES.IDENTIFIER) {
				stack.push(token);
				arg_count.push(0);
				if (were_values.length > 0) {
					were_values.pop();
					were_values.push(true);
				}
				were_values.push(false);
			} else if (token.value == ",") {
				let mismatched = true;
				while (stack.length > 0) {
					if (stack[stack.length - 1].value !== "(") output.push(stack.pop());
					else {
						mismatched = false;
						break;
					}
				}
				if (mismatched) throw "Mismatched parens";
				if (were_values.pop()) {
					arg_count[arg_count.length - 1]++;
					were_values.push(false);
				}
			} else if (token.value == "(") stack.push(token);
			else if (token.value == ")") {
				let mismatched = true;
				while (stack.length > 0) {
					if (stack[stack.length - 1].value !== "(") output.push(stack.pop());
					else {
						mismatched = false;
						break;
					}
				}
				if (mismatched) throw "Mismatched parens";
				stack.pop();
				if (stack.length > 0 && stack[stack.length - 1].type == Parser.TYPES.IDENTIFIER) {
					let f = stack.pop();
					let a = arg_count.pop();
					if (were_values.pop()) a++;
					f.args = a;
					output.push(f);
				}
			} else if (token.type == Parser.TYPES.OPERATOR) {
				while (
					stack.length > 0 &&
					stack[stack.length - 1].type == Parser.TYPES.OPERATOR &&
					((Parser.ASSOC[token.value] == "left" &&
						Parser.PREC[token.value] <= Parser.PREC[stack[stack.length - 1].value]) ||
						(Parser.ASSOC[token.value] == "right" &&
							Parser.PREC[token.value] < Parser.PREC[stack[stack.length - 1].value]))
				)
					output.push(stack.pop());
				stack.push(token);
			}
			// console.log(output, stack, were_values, arg_count);
		}
		while (stack.length > 0) {
			let op = stack.pop();
			if (/[()]/.test(op.type)) throw "Mismatched parens";
			output.push(op);
		}
		return output;
	}
}
