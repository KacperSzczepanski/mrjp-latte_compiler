Kacper Szczepański 418474

Kompilator Latte

Polecenie "make" stworzy program latc i latc_x86. Uruchamianie:
./latc - program wczytany ze standardowego wejścia
./latc ścieżka_do_pliku - program wczytany z pliku

Frontend:
Głównymi narzędziamy użytymi są monady Reader, State oraz Except.
Reader - środowisko typów
State - informacja o zwracanym typie funkcji, która jest teraz typecheckowana
Except - wyjątki

Dodatkowo program sprawdza cały graf ścieżek, czy każda ma odpowiedniego returna.

Program tłumaczy wczytany kod na język asembler x_86 32-bit. Wykorzystuje on takie same monadyczne biblioteki oraz:
IO
standardowe biblioteki list, map, bits i char

Kod jest ponaddto zopytmalizowany metodą LCSE.