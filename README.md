## TLA+ Models for IOx

This repository contains [TLA+] specifications for components used within within
the [IOx] database.

* [Schema cache] - validates cache eventual consistency via anti-entropy /
  differential syncing
* [Health circuit breaker] - liveness checks of the router's lock-free circuit
  breaker primitive

All models are wrong - but some are useful.

[Schema cache]: schema_cache.tla
[Health circuit breaker]: health_circuit.tla

[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[IOx]: https://github.com/influxdata/influxdb_iox/
