default: check

workers := $(or ${workers},1)
tools_path := ~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar
check:
	java -cp ${tools_path} \
	-XX:+UseParallelGC tlc2.TLC SpireSafe.tla -workers ${workers} \
	-tool -modelcheck -config SpireSafe.cfg

faircheck:
	java -cp ${tools_path} \
	-XX:+UseParallelGC tlc2.TLC SpireLive.tla -workers ${workers} \
	-tool -modelcheck -config SpireLive.cfg

sim:
	java -cp ${tools_path} \
	-XX:+UseParallelGC tlc2.TLC SpireSafe.tla -workers ${workers} \
	-tool -simulate -config SpireSafe.cfg

soak: FORCE
	SOAK_CMD="make check workers=${workers}" SOAK_GITPULL=false ./soak.sh

pdf:
	TOOLS_PATH=${tools_path} ./makepdf.sh Spire
	TOOLS_PATH=${tools_path} ./makepdf.sh SpireSafe
	TOOLS_PATH=${tools_path} ./makepdf.sh SpireLive
	TOOLS_PATH=${tools_path} ./makepdf.sh SpireTlaps

FORCE:
