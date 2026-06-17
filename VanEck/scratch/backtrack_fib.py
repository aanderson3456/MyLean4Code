from van_eck_fast import van_eck_fast

def fibonacci_set(limit):
    fibs = [0, 1]
    while True:
        next_fib = fibs[-1] + fibs[-2]
        if next_fib > limit:
            break
        fibs.append(next_fib)
    return set(fibs)

def search_extension(prefix, current_dict, depth, max_depth, fibs):
    if depth == max_depth:
        return True
    
    n = len(prefix)
    prev_val = prefix[-1]
    
    if prev_val in current_dict:
        next_val = (n - 1) - current_dict[prev_val]
    else:
        next_val = 0
        
    if next_val in fibs:
        old_val = current_dict.get(prev_val, None)
        current_dict[prev_val] = n - 1
        prefix.append(next_val)
        
        res = search_extension(prefix, current_dict, depth + 1, max_depth, fibs)
        
        prefix.pop()
        if old_val is None:
            del current_dict[prev_val]
        else:
            current_dict[prev_val] = old_val
            
        return res
    else:
        return False

def test_n0(N0, max_depth):
    prefix = van_eck_fast(N0)
    if not prefix:
        prefix = [0]
    
    last_seen = {}
    for i in range(len(prefix) - 1):
        last_seen[prefix[i]] = i
        
    fibs = fibonacci_set(N0 + max_depth + 10)
    return search_extension(prefix, last_seen, 0, max_depth, fibs)

if __name__ == "__main__":
    max_depth = 100
    found_any = False
    for N0 in range(1, 1000):
        if test_n0(N0, max_depth):
            print(f"Found valid starting index N0 = {N0}!")
            found_any = True
            break
    if not found_any:
        print("No N0 < 1000 can be extended by 100 steps.")
