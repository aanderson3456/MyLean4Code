def find_sequences(L):
    # We want to find a sequence a_0, a_1, ..., a_{L-1}
    # where all elements are odd or 0, and it follows the Van Eck rule.
    # We will represent the sequence as a list of integers.
    # Since we can choose any unused odd number for a "new" term, we can just use 0 and positive odd numbers.
    # To keep track of "new" numbers, we can use a set of seen numbers.
    
    results = []
    
    def search(seq, last_seen):
        n = len(seq)
        if n == L:
            results.append(list(seq))
            return
            
        # The next term to determine is seq[n] based on seq[n-1]
        prev = seq[-1]
        
        # Check if prev has occurred before index n-1
        # To do this, we need to know the last occurrence of prev before n-1.
        # Let's find it.
        prev_occurrences = [i for i, x in enumerate(seq[:-1]) if x == prev]
        
        if not prev_occurrences:
            # prev is new!
            # So the next term MUST be 0.
            next_val = 0
            if next_val == 0 or next_val % 2 == 1:
                seq.append(next_val)
                search(seq, last_seen)
                seq.pop()
        else:
            # prev has occurred before.
            # The next term MUST be the distance: (n - 1) - prev_occurrences[-1]
            next_val = (n - 1) - prev_occurrences[-1]
            if next_val == 0 or next_val % 2 == 1:
                seq.append(next_val)
                search(seq, last_seen)
                seq.pop()

    # We start with seq of length 1.
    # seq[0] can be 0 or any positive odd number.
    # Since all positive odd numbers behave identically when they are new,
    # we can just test seq[0] = 0 and seq[0] = 1 (representing any new odd number).
    
    for start in [0, 1]:
        search([start], {})
        
    return results

def main():
    for L in range(1, 10):
        res = find_sequences(L)
        print(f"Length {L}: found {len(res)} valid sequences.")
        for r in res[:5]:
            print("  ", r)

if __name__ == "__main__":
    main()

