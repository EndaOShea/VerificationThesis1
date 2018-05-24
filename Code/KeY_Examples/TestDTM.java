class TestDTM
{
	/*@ public normal_behavior
	@ requires n>0;
	@ ensures \result == (\sum{int i; 0<=i && i<n; i})
	@ measured_by n;
	@ modifies n;
	@*/
	public int sum(int n) {
		if (n >= 1) {
			return sum(n - 1) + n;
		}
		return n;
	}
}