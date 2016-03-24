default: sortcensus

CCFLAGS=-O3 -std=c++11 -pthread
OBJS=sortcensus.o threadpool.o
clean:
	rm -f sortcensus $(OBJS)

debug: CCFLAGS += -g
debug: default

sortcensus: $(OBJS)
	g++ $(CCFLAGS) $(LIBS) \
		`regina-engine-config --cflags --libs` \
		-o $@ $^

%.o: %.cpp threadpool.h
	g++ $(CCFLAGS) `regina-engine-config --cflags` \
		-c -o $@ $<

