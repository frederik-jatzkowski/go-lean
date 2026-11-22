package assumed_quota

var configuredQuota int64 = 10

//golean:assume quotaBound : ReadQuota ≤ 10
func ReadQuota() int64 {
	return configuredQuota
}

//golean:abstract ReadQuota
//golean:verify deniesEleven : CanSpend 11 = false
func CanSpend(cost int64) bool {
	return cost <= ReadQuota()
}
