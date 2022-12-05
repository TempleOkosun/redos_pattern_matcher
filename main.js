// import timer
const { performance } = require('perf_hooks')

/* Algorithm - Sketch */

// below is a reference example of a loop-in-loop vulnerability
// and the corresponding match string and attack string
const regexpTree = require('regexp-tree')

// Test 1 where subexpressions are base cases
let test_regex = regexpTree.toRegExp(/^((b\D)*ba([a-z]a)*)*$/)
let ts_1 = 'bababababababababababababababababababababa' // match string
let ts_2 = 'bababababababababababababababababababababab' // attack string

let t1_start = performance.now()
// The first match should be quick. The second is slow due to the loop-in-loop pattern
// and the fact that the pattern does not match the provided text (exponential backtracking).
let ts_1_result = test_regex.test(ts_1)
let t1_end = performance.now()
console.log('Traditional match 1: ', ts_1_result)
console.log(`T1 execution time: ${t1_end - t1_start} \n`)

let t2_start = performance.now()
let ts_2_result = test_regex.test(ts_2)
console.log('Traditional match 2: ', ts_2_result)
let t2_end = performance.now()
console.log(`T2 execution time: ${t2_end - t2_start} \n`)

// Test 2 where subexpressions are vulnerable
test_regex = regexpTree.toRegExp(
  /^(((b\D)*ba([a-z]a)*)*((b\D)*ba([a-z]a)*)*)*$/
);
ts_1 = 'babababababababababababa';
ts_2 = 'babababababababababababab';

t1_start = performance.now()
ts_1_result = test_regex.test(ts_1)
t1_end = performance.now()
console.log('Traditional match 3: ', ts_1_result)
console.log(`T3 execution time: ${t1_end - t1_start} \n`)


t2_start = performance.now()
ts_2_result = test_regex.test(ts_2)
t2_end = performance.now()
console.log('Traditional match 4: ', ts_2_result)
console.log(`T4 execution time: ${t2_end - t2_start} \n`)

// Structure that represents an atomic match section
/*
 * @param pattern: RegExp literal
 *        count_min: int
 *        count_max: int
 */
class SubExpr {
  constructor(pattern, count_min, count_max) {
    this.pattern = pattern;
    this.count_min = count_min;
    this.count_max = count_max;
    this.sequence = null;
    this.index = -1;
    this.matchstarts = new Set();
    this.matchpoints = new Set(); // array of lenth 2 arrays consisting of start and end index matches
    this.range_matchpoints = new Set(); // Subset of matchpoints that appear within the count_min, count_max
    // range of this.sequence
  }

  /*
   * Finds where to start pattern matching in a string. Will start at the earliest match
   * that has not been checked yet for the previous sub expression in the pattern.
   *
   * @param list_of_subexpr: list of SubExpr
   *
   * @returns set of int
   */
  findEarliest() {
    // Returns a set of all the indices to start at next
    const retval = new Set();

    let i =
      this.index == 0
        ? this.sequence.length - 1
        : Math.abs((this.index - 1) % this.sequence.length);
    for (
      ;
      i != this.index;
      i =
        i == 0
          ? this.sequence.length - 1
          : Math.abs((i - 1) % this.sequence.length)
    ) {
      // Find the earliest SubExpr that count min greater than 0
      let previous = this.sequence.get(i);

      // Can appear after this subexpression. However, may not.
      for (const end of previous.matchpoints) {
        if (!this.matchstarts.has(end)) {
          retval.add(end); // Start at the end of the previous match
        }
      }

      // Since this subexpression must be matched at least once, we must appear after it
      if (previous.count_min > 0) {
        break;
      }
    }

    if (i == this.index) {
      // Must also add our matchpoints
      for (const end of this.matchpoints) {
        if (!this.matchstarts.has(end)) {
          retval.add(end);
        }
      }

      // Is this needed?
      if (this.matchpoints.size == 0) {
        retval.add(0);
      }
    }

    return retval;
  }

  /*
   * Runs matches on the text starting at the last index matched, but not exceeding
   * the max match count. If start is true, start at index zero.
   *
   * @param start: bool
   *        range: bool - true iff add to range_matchpoints
   */
  runMatch(start, range) {
    let matches_found = false;
    let change = false;
    let start_index;

    if (start) {
      start_index = new Set();
      start_index.add(0);
    } else {
      start_index = this.findEarliest();
    }

    if (start_index.size == 0) {
      return false;
    }

    // console.log(start_index);

    // Match as much as possible
    for (let st of start_index) {
      let temp = new Set(this.matchpoints);
      let temp2 = new Set(this.matchstarts);
      let i = 0;
      let change_set = change;

      for (; i < this.count_max; i++) {
        let match_string = this.sequence.getText().slice(st);
        let match_res = this.pattern.exec(match_string);

        if (match_res == null || match_res['index'] != 0) {
          // Must match from start of the string
          break;
        }

        // Remember the matches
        let match_text = match_res[0];
        this.matchpoints.add(st + match_text.length);
        this.matchstarts.add(st);
        if (range) {
          this.range_matchpoints.add(st + match_text.length);
        }
        change = true;

        // console.log(this.index, "match", (st + match_text.length).toString());

        // Increment to the next index
        st += match_text.length;
      }

      // Make sure enough matches were found. If not, reset matchpoints
      if (i < this.count_min) {
        this.matchpoints = new Set(temp);
        this.matchstarts = new Set(temp2);
        change = change_set;
      } else {
        matches_found = true;
      }
    }

    // console.log("Final", this.index.toString(), this.matchstarts, this.matchpoints);

    // Return whether or not matches were found
    return [matches_found, change];
  }
}

// Expr is a SubExpr where the pattern is vulnerable. That is,
// the pattern is Loop-in-Loop, Loop-after-Loop and/or Branch-in-Loop.
// This allows vulnerable expressions to be nested within other
// expressions.
class Expr extends SubExpr {
  constructor(count_min, count_max) {
    super(/./, count_min, count_max);
    this.items = []; // In order expressions to be matched
    this.text = ''; // Text to be matched
    this.length = 0;
    this.final = false;
  }

  /*
   * Inserts a SubExpr
   *
   * @param item: SubExpr
   */
  insert(item) {
    // Make copy of object
    let temp = Object.assign(Object.create(Object.getPrototypeOf(item)), item);
    temp.index = this.items.length;
    temp.sequence = this;
    this.length = this.items.length + 1;
    this.items.push(temp);
  }

  /*
   * Retreives SubExpr at index i
   *
   * @param index: int
   */
  get(index) {
    return this.items[index];
  }

  /*
   * Sets match text to t.
   *
   * @param t: string
   */
  setText(t) {
    this.text = t;
    for (let i = 0; i < this.items.length; i++) {
      if (this.items[i] instanceof Expr) {
        this.items[i].setText(t);
      }
    }
  }

  /*
   * Gets match text t.
   *
   * @returns string
   */
  getText(t) {
    return this.text;
  }

  // Overload SubExpr methods

  /* Executes the matching algorithm on the subexpressions.
   * This method must return the index of all valid endpoints
   * of a match.
   * @returns [0] - bool - true for match and false for no match
   *          [1] - set of int - endpoints of valid matches
   */
  matchChildren(start) {
    // Reset values for all subexpressions
    for (let i = 0; i < this.items.length; i++) {
      this.items[i].matchpoints = new Set();
      this.items[i].matchstarts = new Set();
      this.items[i].range_matchpoints = new Set();
    }

    let missed_matches = 0;
    let range_counter = 0;
    for (
      let i = 0;
      missed_matches < this.items.length;
      i = Math.abs((i + 1) % this.items.length)
    ) {
      let range =
        Math.floor(range_counter / this.items.length) + 1 >= this.count_min &&
        Math.floor(range_counter / this.items.length) + 1 <= this.count_max;
      let fm = this.items[i].runMatch(start, range);
      missed_matches = fm[1] ? 0 : missed_matches + 1;
      start = false;
      range_counter++;
    }

    // Print resulting matches
    // for (let i = 0; i < this.items.length; i++) {
    //   console.log(this.items[i].range_matchpoints);
    // }

    let found_match = false;
    let match_set = new Set();
    for (let i = this.items.length - 1; i >= 0; i--) {
      for (const j of this.items[i].range_matchpoints) {
        // Find all the matches we have
        match_set.add(j);
        found_match = true;
      }

      // If this subexpression must be matched at least once, we can stop checking.
      // Either this subexpression must appear on the end of a match, or some subexpression
      // that has already been checked.
      if (this.items[i].count_min > 0) {
        break;
      }
    }

    return [found_match, match_set];
  }

  /*
   * Runs matches on the text starting at the last index matched, but not exceeding
   * the max match count. If start is true, start at index zero.
   *
   * @param start: bool
   *        range: bool - true iff add to range_matchpoints
   */
  runMatch(start, range) {
    let start_index;
    let change = false;

    if (start) {
      start_index = new Set();
      start_index.add(0);
    } else {
      start_index = this.findEarliest();
    }

    if (start_index.size == 0) {
      return false;
    }

    // Compute n*n matrix where M[i][j] is true iff we can match this expression
    // starting at index i and going to index j.
    let text_len = this.getText().length;
    const M = [...new Array(text_len + 1)].map(item =>
      new Array(text_len + 1).fill(false)
    );

    // Compute matrix
    for (let i = 0; i < text_len; i++) {
      // Save values
      let old_string = this.getText();
      this.setText(this.getText().slice(i));

      // perform match
      let match_res = this.matchChildren(true);

      // reset text
      this.setText(old_string);

      for (const endpoint of match_res[1]) {
        M[i][endpoint + i] = true;
      }
    }
    // console.log(M);

    // Indicate the min and max count at each index
    const track_counter = [...new Array(text_len + 1)].map(item => [-1, 0]);

    // Match as much as possible
    let i = 0;
    for (; i < this.count_max; i++) {
      let si_copy = new Set();

      for (const st of start_index) {
        /*
         * This is different than the case with SubExpr. For SubExpr, there
         * we will end up matching and ending at only one end index when matching
         * as much as possible. In this case, we can end up with multiple. Therefore,
         * we need to loop through at try to match up to "count_max" for each of
         * these endpoints. Need to keep seperate values for the number of loops
         * to match at each point. Always try matching at both max and min for
         * each of these ends. That way, you can properly check the min amount of
         * matches you can have and the max. Then, you can compare to final boundaries
         * of [this.count_min, this.count_max].
         */

        for (let j = 0; j < text_len + 1; j++) {
          if (M[st][j]) {
            // Update counters
            if (track_counter[j][0] < 0) {
              track_counter[j][0] = i + 1;
            }
            track_counter[j][1] = i + 1;

            if (
              i + 1 >= this.count_min &&
              i + 1 <= this.count_max &&
              !this.matchpoints.has(j)
            ) {
              // add to matchpoints
              change = true;
              this.matchpoints.add(j);
              this.matchstarts.add(st);
              if (range) {
                this.range_matchpoints.add(j);
              }
            }

            // Indicate we can reach that match
            si_copy.add(j);
          }
        }
      }

      if (si_copy.size == 0) {
        break; // no more matches to try
      }
      start_index = si_copy;
    }

    // Update the match points
    // console.log(this.matchpoints);
    // console.log(track_counter);

    this.final = M[0][text_len];

    let found_match = i >= this.count_min;

    // Return whether or not matches were found
    return [found_match, change];
  }
}

// Tests
// This will try to match ^((b\D)*ba([a-z]a)*)*$
// We do this by breaking down the expression into three parts
//
// 1. (b\D){0,infinity}
// 2. (ba){1}
// 3. ([a-z]a){0,infinity}
//
// All parts wrapped by a looping operator. We then preform the less vulnerable matching
// algorithm.
//
// This is a vulnerable expression that leads to catastrophic backtracking when
// no match is found on: bababababababababababababababababababa
// However, this algorithm detects there is no match without the
// catastrohpic backtracking.

//1. Good Match

console.log('Start Tests with implemented algorithm')

let group = new Expr(0, 10)
group.setText('bababababababababababababababababababababa')
let exp1 = new SubExpr(/b\D/, 0, 30)
let exp2 = new SubExpr(/ba/, 1, 1)
let exp3 = new SubExpr(/[a-z]a/, 0, 30)

// add expressions to sequences
group.insert(exp1)
group.insert(exp2)
group.insert(exp3)

let final1_start = performance.now()
let final_match = group.runMatch(true, false)
let final1_end = performance.now()
console.log('Final match 1: ', group.final)
console.log(`Final1 execution time: ${final1_end - final1_start} \n`)

// 2. Vulnerable
let group2 = new Expr(0, 10)
group2.setText('bababababababababababababababababababababab')
exp1 = new SubExpr(/b\D/, 0, 30)
exp2 = new SubExpr(/ba/, 1, 1)
exp3 = new SubExpr(/[a-z]a/, 0, 30)

// add expressions to sequences
group2.insert(exp1)
group2.insert(exp2)
group2.insert(exp3)

let final2_start = performance.now()
final_match = group2.runMatch(true, false)
let final2_end = performance.now()
console.log('Final match 2: ', group2.final)
console.log(`Final2 execution time: ${final2_end - final2_start} \n`)

// Test recursive vulnerable patterns
let group5 = new Expr(0, 10);
group5.insert(group);
group5.insert(group);

group5.setText('babababababababababababa');
final1_start = performance.now()
final_match = group5.runMatch(true, false);
final1_end = performance.now()
console.log('Final match: ', group5.final);
console.log(`Final3 execution time: ${final1_end - final1_start} \n`)

group5.setText('babababababababababababab');
final2_start = performance.now()
final_match = group5.runMatch(true, false);
final2_end = performance.now()
console.log('Final match: ', group5.final);
console.log(`Final2 execution time: ${final2_end - final2_start} \n`)

// // Check correctness. Should not match
// let group3 = new Expr(0, 10)
// group3.setText('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa')
// exp1 = new SubExpr(/aaaa/, 1, 1)
// exp2 = new SubExpr(/a/, 1, 3)
// exp3 = new SubExpr(/aaa/, 1, 1)

// // add expressions to sequences
// group3.insert(exp1)
// group3.insert(exp2)
// group3.insert(exp3)

// final_match = group3.runMatch(true, false)
// console.log('Final match 3: ', group3.final)

// // Check correctness. Should match
// let group4 = new Expr(0, 10)
// group4.setText('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa')
// exp1 = new SubExpr(/aaaa/, 1, 1)
// exp2 = new SubExpr(/a/, 1, 3)
// exp3 = new SubExpr(/aaa/, 1, 1)

// // add expressions to sequences
// group4.insert(exp1)
// group4.insert(exp2)
// group4.insert(exp3)

// final_match = group4.runMatch(true, false)
// console.log('Final match 4: ', group4.final)
