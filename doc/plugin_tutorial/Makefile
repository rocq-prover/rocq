
TUTOS:= \
  tuto0 \
  tuto1 \
  tuto2 \
  tuto3 \
  tuto4

all: $(TUTOS)

.PHONY: $(TUTOS) all

$(TUTOS): %:
	+$(MAKE) -C $@

CLEANS:=$(addsuffix -clean, $(TUTOS))
.PHONY: clean $(CLEANS)

clean: $(CLEANS)

%-clean:
	+$(MAKE) -C $* clean
