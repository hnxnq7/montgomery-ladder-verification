From quartz.lang Require Import Syntax sv.
From LadderQuartz Require Import sv_printer masked_controller_native_export.
From Stdlib Require Import String.
Local Open Scope string_scope.

Goal True. idtac "STAGE canonical-native256-print-start". exact I. Qed.
Compute SVPrinterDList.render (@MaskedControllerNativeExport.native256 sv.var sv.fn).
Goal True. idtac "STAGE canonical-native256-print-complete". exact I. Qed.
