from van_eck_fast import van_eck_fast

def find_longest_odd_block(limit):
    print(f"Generating first {limit} terms of the Van Eck sequence...")
    a = van_eck_fast(limit)
    print("Generation complete. Searching for longest block of odd/zero terms...")
    
    max_len = 0
    best_start = -1
    current_len = 0
    current_start = -1
    
    for i, val in enumerate(a):
        if val == 0 or val % 2 == 1:
            if current_len == 0:
                current_start = i
            current_len += 1
        else:
            if current_len > max_len:
                max_len = current_len
                best_start = current_start
            current_len = 0
            
    if current_len > max_len:
        max_len = current_len
        best_start = current_start
        
    print(f"Longest block length: {max_len}")
    print(f"Starts at index: {best_start}")
    if best_start != -1:
        print(f"Block terms: {a[best_start:best_start + max_len + 3]}")

if __name__ == "__main__":
    find_longest_odd_block(1000000)
