import sys

def find_longest_odd_block_huge(limit):
    print(f"Scanning first {limit} terms...")
    last_seen = {}
    
    current_val = 0
    max_len = 0
    best_start = -1
    current_len = 0
    current_start = -1
    
    for i in range(limit):
        if i > 0 and i % 10000000 == 0:
            print(f"  Processed {i} terms... Current max length: {max_len}")
            
        # Check if current_val is odd or 0
        if current_val == 0 or current_val % 2 == 1:
            if current_len == 0:
                current_start = i
            current_len += 1
        else:
            if current_len > max_len:
                max_len = current_len
                best_start = current_start
            current_len = 0
            
        # Compute next term
        if current_val in last_seen:
            next_val = i - last_seen[current_val]
        else:
            next_val = 0
            
        last_seen[current_val] = i
        current_val = next_val
        
    if current_len > max_len:
        max_len = current_len
        best_start = current_start
        
    print(f"\nFinal results for {limit} terms:")
    print(f"Longest block length: {max_len}")
    print(f"Starts at index: {best_start}")
    
    # Re-run to get the block terms
    if best_start != -1:
        print("Re-running to extract block terms...")
        last_seen_extract = {}
        curr = 0
        block = []
        for i in range(best_start + max_len + 3):
            if i >= best_start:
                block.append(curr)
            # Compute next term
            if curr in last_seen_extract:
                nxt = i - last_seen_extract[curr]
            else:
                nxt = 0
            last_seen_extract[curr] = i
            curr = nxt
        print(f"Block terms: {block}")

if __name__ == "__main__":
    limit = 50000000
    if len(sys.argv) > 1:
        limit = int(sys.argv[1])
    find_longest_odd_block_huge(limit)
