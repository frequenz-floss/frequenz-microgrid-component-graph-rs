# Frequenz Component Graph Release Notes

## Upgrading

- `consumer_formula()` and `producer_formula()` no longer clamp their results. The clamps assumed the sign of active power, so they replaced valid values of other metrics, such as reactive power, with zero.
  - The consumer formula was wrapped in `MAX(…, 0.0)`. It can now be negative, for example when unmodeled production or a measurement mismatch is larger than the consumption. To get the old result, wrap the formula as `MAX(<formula>, 0.0)`.
  - Each producer term was wrapped in `MIN(…, 0.0)`. A producer that draws power now adds a positive value instead of zero, so the total can be positive. For example, PV producing 10 kW and a CHP drawing 2 kW used to give -10 kW and now give -8 kW. There is one exception: when the two share a meter below the grid meter, that meter sends data, and `disable_fallback_components` is off, the meter measures them together, so they gave -8 kW before too. Wrapping the total as `MIN(<formula>, 0.0)` clamps the total at zero, but it still differs from the old result when one producer draws power while another produces.
  - With `include_phantom_loads_in_consumer_formula`, the consumer formula is unchanged: it still clamps each of its terms at zero.
