@echo off
call "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
if errorlevel 1 (echo [prof] vcvars64 not found & exit /b 1)
if not exist build mkdir build
REM DMMSY upstream compiled verbatim from the ref-dmmsy submodule via the port header
cl /nologo /std:c17 /W3 /wd4244 /wd4267 /I include /O2 /Ob3 /DNDEBUG /DCHD_PROF /fp:precise /GS- /FI dmmsy_port.h /c ref-dmmsy\src\common.c ref-dmmsy\src\dmmsy_opt.c /Fo:build\ || exit /b 1
cl /nologo /std:c17 /W3 /wd4244 /wd4267 /I include /O2 /Ob3 /DNDEBUG /DCHD_PROF /fp:precise /GS- src\benchmark.c src\common.c src\dijkstra.c src\bellman_ford.c src\chd.c build\common.obj build\dmmsy_opt.obj /Fe:build\chd_bench_prof.exe || exit /b 1
echo [prof] build\chd_bench_prof.exe
