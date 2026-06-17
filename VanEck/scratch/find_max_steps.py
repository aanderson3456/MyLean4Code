from van_eck_fast import van_eck_fast

def fibonacci_set(limit):
    fibs = [0, 1]
    while True:
        next_fib = fibs[-1] + fibs[-2]
        if next_fib > limit:
            break
        fibs.append(next_fib)
    return set(fibs)

def count_steps_until_non_fib(N0):
    prefix = van_eck_fast(N0)
    if not prefix:
        prefix = [0]
    
    last_seen = {}
    for i in range(len(prefix) - 1):
        last_seen[prefix[i]] = i
        
    fibs = fibonacci_set(N0 + 1000)
    
    steps = 0
    current_prefix = list(prefix)
    while True:
        n = len(current_prefix)
        prev_val = current_prefix[-1]
        
        if prev_val in last_seen:
            next_val = (n - 1) - last_seen[prev_val]
        else:
            next_val = 0
            
        if next_val in fibs:
            last_seen[prev_val] = n - 1
            current_prefix.append(next_val)
            steps += 1
        else:
            return steps, next_val

if __name__ == "__main__":
    for N0 in range(1, 30):
        steps, bad_val = count_steps_until_non_fib(N0)
        print(f"N0 = {N0}: extended {steps} steps, stopped by {bad_val}")
