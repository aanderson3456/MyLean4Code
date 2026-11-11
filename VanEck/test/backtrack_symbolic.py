def solve():
    # We want to find the maximum length L of a sequence a_0, ..., a_{L-1}
    # where:
    # 1. Every term is 0 or an odd integer.
    # 2. It satisfies the Van Eck recurrence.
    #
    # We represent the sequence as a list where each element is either:
    # - an integer (like 0, 1, 3, ...)
    # - a symbolic variable representing a new, unassigned odd integer.
    #
    # Let's write a backtracking search.
    # At each step, we have:
    # - seq: list of terms of length n
    # - sym_map: dict mapping symbolic variables (e.g., 'x0', 'x1') to their values (None if unassigned, or an odd integer)
    # - last_seen: dict mapping each value (integer or symbol) to its last seen index.
    
    max_len = 0
    best_seq = []
    
    def search(seq, sym_values, last_seen, next_sym_id):
        nonlocal max_len, best_seq
        n = len(seq)
        if n > max_len:
            max_len = n
            best_seq = list(seq)
            print(f"New max length {max_len}: {best_seq} with sym_values={sym_values}")
            
        # The term at n-1 is seq[-1].
        # We need to determine seq[n].
        prev = seq[-1]
        
        # We need to find the last occurrence of prev.
        # Since prev could be a symbol or a concrete value:
        # Let's resolve what prev actually is.
        # If prev is a symbol:
        #   Case 1: prev has a concrete value assigned.
        #     Then we treat prev as that concrete value.
        #   Case 2: prev does not have a concrete value assigned.
        #     Since it's a symbol, its first occurrence is at some index.
        #     If that first occurrence is n-1, then it is NEW, so the next value must be 0.
        #     If it was seen before, wait: a symbol represents a "new" number when first introduced.
        #     So by definition, the first time a symbol appears in seq, it has not appeared before.
        #     Wait! If seq[-1] is a symbol, it's either:
        #     - Its first appearance in the sequence: then it is new, so seq[n] = 0.
        #     - Not its first appearance: then it must have appeared before.
        #       Wait, but in our construction, we only introduce a symbol as a "new" term.
        #       So its first appearance is when we decided it is new.
        #       If we repeat it later, we would have set seq[k] to that symbol.
        #       But wait, can we choose to set seq[k] to an existing symbol?
        #       Only if the Van Eck recurrence forced it!
        #       So seq[k] is determined by the recurrence.
        
        # Let's do this more simply:
        # Let's represent seq as a list of integers.
        # We can assign actual odd integers to the "new" terms.
        # Since the actual odd integers we can choose are from {1, 3, 5, 7, ...},
        # at each step where we need a "new" term, we can either:
        # - Choose a specific odd integer that has NOT been used in the sequence yet.
        # Wait, does it matter which odd integer we choose?
        # It only matters if that integer is generated later as a lookback distance!
        # E.g., if we choose a_0 = 3, and later a lookback distance of 3 is generated, then they match.
        # If we chose a_0 = 99, and later a lookback distance of 3 is generated, they wouldn't match.
        # But since the lookback distance is at most the current index, the possible lookback distances
        # at index n are all integers < n.
        # So any new term we introduce can only ever match a future lookback distance if that lookback distance is odd and < L.
        # Therefore, the set of "useful" values for a new term is very small:
        # It can only be one of the odd integers < L, or a "generic" large odd integer (which will never be matched).
        # So for a fixed maximum length L (say L = 10), when we need a new term, we can try:
        # - Each odd integer in {1, 3, 5, ..., 2*L} that has not been used yet.
        # - Plus one "generic" large odd integer (e.g., 999) representing "any other odd integer".
        # This is a completely rigorous and finite search!
        pass

if __name__ == "__main__":
    solve()
