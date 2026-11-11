def van_eck_fast(n):
    """
    Generates the first n terms of the Van Eck sequence.
    Time Complexity: O(n)
    Space Complexity: O(n)
    """
    if n <= 0:
        return []
    a = [0] * n
    last_seen = {}
    for i in range(n - 1):
        val = a[i]
        if val in last_seen:
            a[i + 1] = i - last_seen[val]
        else:
            a[i + 1] = 0
        last_seen[val] = i
    return a

if __name__ == "__main__":
    # Example: print the first 100 terms of the Van Eck sequence
    print(van_eck_fast(100))
