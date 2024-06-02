theory L4_Config
  imports "../Abs/L4_Abs"
begin

definition "max_nat = (2^32-1::nat)"
definition "max_int = (2^32-1::int)"

definition "MAX_PRIO = 255"
definition "ROOT_PRIORITY = MAX_PRIO"
definition "DEFAULT_PRIORITY = 100"
definition "DEFAULT_TOTAL_QUANTUM = 0"
definition "DEFAULT_TIMESLICE_LENGTH = 10000"

end