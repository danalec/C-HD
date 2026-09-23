@echo off
call "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
if errorlevel 1 (echo [asan] vcvars64 not found & exit /b 1)
if not exist build mkdir build
cl /nologo /std:c17 /W3 /wd4244 /wd4267 /I include /Od /Zi /fsanitize=address /DCHD_DEBUG tests\test_chd.c src\common.c src\dijkstra.c src\bellman_ford.c src\chd.c /Fe:build\test_asan.exe || exit /b 1
echo [asan] build\test_asan.exe
