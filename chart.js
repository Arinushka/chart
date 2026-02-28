class CandlestickChart {
    constructor(canvasId) {
        this.canvas = document.getElementById(canvasId);
        if (!this.canvas) {
            console.error('Canvas element not found!');
            return;
        }
        this.ctx = this.canvas.getContext('2d');
        
        // Chart dimensions (логические пиксели для координат; буфер канваса = logical * dpr для чёткости при масштабе)
        this.dpr = 1;
        this.logicalWidth = 0;
        this.logicalHeight = 0;
        this.padding = { top: 20, right: 80, bottom: 80, left: 10 }; // Increased bottom for volume
        this.chartWidth = 0;
        this.chartHeight = 0;
        this.chartEndPositionRatio = 2 / 3; // окончание графика (последняя свеча) на 2/3 ширины экрана
        this.volumeHeight = 50; // Height reserved for volume bars
        
        // Price range - will be calculated from data
        this.minPrice = 0;
        this.maxPrice = 0;
        this.priceRange = 0;
        
        // Price levels - will be updated after data load
        this.priceLevels = [];
        
        // Data loading state
        this.candles = [];
        this.volumeData = [];
        this.symbol = 'BTCUSDT'; // Default symbol
        this.market = 'spot'; // spot | futures
        this.interval = '1d'; // Default interval (1 day)
        this.exchangeName = 'Binance'; // Биржа — источник данных
        this.ws = null; // WebSocket connection
        this.wsReconnectAttempts = 0;
        this.maxReconnectAttempts = 5;
        
        // Drawing mode state
        this.drawingMode = false;
        this.horizontalLineMode = false;
        this.alertMode = false; // Alert: один клик — прерывистый луч от точки до конца графика
        this.rectangleMode = false;
        this.rulerMode = false;
        this.drawnLines = []; // Array to store drawn lines (brush tool)
        this.horizontalLines = []; // Array to store horizontal rays
        this.rectangles = []; // Array to store rectangles
        this.rulerSelections = []; // Array to store ruler selections with data
        this.currentLine = null; // Current line being drawn (first point)
        this.currentRectangle = null; // Current rectangle being drawn (first point)
        this.currentRulerSelection = null; // Current ruler selection being drawn
        this.tempPoint = null; // Temporary point for preview
        this.drawingsVisible = true; // Toggle visibility of all drawn elements (lines, rectangles, ruler, etc.)
        this.selectedDrawing = null; // { type: 'line'|'rect'|'ray'|'ruler', index: number } — выделенный элемент для удаления по Delete/Backspace
        
        // Panning state
        this.isPanning = false;
        this.panStartX = 0;
        this.panStartY = 0;
        // Zoom by drag (right mouse): сдвиг по горизонтали — масштаб по времени, по вертикали — по цене
        this.isZoomDragging = false;
        this.zoomDragStartX = 0;
        this.zoomDragStartY = 0;
        this.zoomDragStartTimeRange = 0;
        this.zoomDragStartPriceRange = 0;
        this.zoomDragStartVisible = null;
        this.panStartVisibleStartTime = 0;
        this.panStartVisibleEndTime = 0;
        this.panStartVisibleMinPrice = 0;
        this.panStartVisibleMaxPrice = 0;
        
        // Time range - will be set after data load
        this.startTime = 0;
        this.endTime = 0;
        this.timeRange = 0;
        
        // Zoom and pan state - will be set after data load
        this.zoomLevel = 1.0;
        this.visibleStartTime = 0;
        this.visibleEndTime = 0;
        this.visibleMinPrice = 0;
        this.visibleMaxPrice = 0;
        this.axisZoomUsed = false; // true, если пользователь масштабировал по осям (для показа кнопки «Сбросить масштаб»)
        
        // Indicators (MA, EMA, etc.) - main chart overlay
        this.activeIndicators = {
            ma: [],   // [{ period, source, color }, ...]
            ema: [],  // [{ period, source, color }, ...]
            wma: [],
            boll: null,
            vwap: null,
            sar: null,
            macd: null,  // { fast, slow, signal, colorMacd, colorSignal, colorHist }
            rsi: null,   // { period, color }
            trix: null,  // { period, color }
            super: null,  // { period, multiplier, color }
            // Субиндикаторы (вкладка «Субиндикатор»)
            subVol: null,   // { mavol1: { en, period, lineWidth, color }, mavol2: {...}, long, short }
            subMacd: null, subRsi: null, subMfi: null, subKdj: null, subObv: null,
            subCci: null, subStochRsi: null, subWr: null, subDmi: null, subMtm: null, subEmv: null
        };
        this.valuesConfig = {
            density: { enabled: false, color: '#ff5252' }
        };
        this.levelsConfig = {
            support: { enabled: false, color: '#00bcd4' },
            resistance: { enabled: false, color: '#ff5252' }
        };
        this.densityData = null; // { currentPrice, bidDensity, askDensity, dailyVolume }
        this.densityVolumePercentage = 2; // Порог плотности, % от суточного объема
        this.densityDepth = 500; // Глубина стакана
        this.densityUpdateTimer = null;
        
        // Bind resize
        window.addEventListener('resize', () => this.resize());
        
        // Bind mouse events for drawing
        this.setupDrawingEvents();
        
        // Bind wheel event for zooming
        this.setupZoomEvents();
        
        // Контекстное меню «Сбросить масштаб» по правому клику
        this.setupResetZoomContextMenu();
        
        // Сразу показываем биржу — источник данных (как на первом скриншоте)
        const exchangeEl = document.getElementById('exchangeName');
        if (exchangeEl) exchangeEl.textContent = this.exchangeName || '—';
        
        // Load data from Binance API
        this.loadBinanceData();
    }
    
    setupZoomEvents() {
        this.canvas.addEventListener('wheel', (e) => {
            e.preventDefault();
            
            // Get mouse position relative to canvas
            const rect = this.canvas.getBoundingClientRect();
            const mouseX = e.clientX - rect.left;
            const mouseY = e.clientY - rect.top;
            
            // Check if mouse is over chart area (excluding volume)
            const chartAreaHeight = this.chartHeight - this.volumeHeight;
            if (mouseX < this.padding.left || mouseX > this.logicalWidth - this.padding.right ||
                mouseY < this.padding.top || mouseY > this.padding.top + chartAreaHeight) {
                return;
            }
            
            // Колёсико: общий зум. При прокрутке назад — уменьшение графика и появление свободного пространства вокруг.
            const zoomFactor = e.deltaY > 0 ? 0.9 : 1.1;
            const currentTimeRange = this.visibleEndTime - this.visibleStartTime;
            const currentPriceRange = this.visibleMaxPrice - this.visibleMinPrice;
            const mouseTime = this.xToTime(mouseX);
            const mousePrice = this.yToPrice(mouseY);
            const normalizedX = this.chartWidth > 0 ? (mouseX - this.padding.left) / this.chartWidth : 0.5;
            const normalizedY = (this.padding.top + chartAreaHeight - mouseY) / chartAreaHeight;
            const newTimeRange = Math.max(this.timeRange * 0.005, currentTimeRange / zoomFactor);
            const newPriceRange = Math.max(this.priceRange * 0.005, currentPriceRange / zoomFactor);
            let newStartTime = mouseTime - currentTimeRange * normalizedX * (newTimeRange / currentTimeRange);
            let newEndTime = newStartTime + newTimeRange;
            let newMinPrice = mousePrice - currentPriceRange * normalizedY * (newPriceRange / currentPriceRange);
            let newMaxPrice = newMinPrice + newPriceRange;
            this.zoomLevel *= zoomFactor;
            this.visibleStartTime = newStartTime;
            this.visibleEndTime = newEndTime;
            this.visibleMinPrice = newMinPrice;
            this.visibleMaxPrice = newMaxPrice;
            this.draw();
        });
    }
    
    setupResetZoomContextMenu() {
        const chartInstance = this;
        const chartArea = this.canvas.parentElement;
        if (!chartArea) return;
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'chart-reset-zoom-corner-btn';
        btn.textContent = 'Сбросить масштаб';
        btn.style.display = 'none';
        chartArea.appendChild(btn);
        this.resetZoomBtnEl = btn;
        btn.addEventListener('click', () => {
            chartInstance.resetZoomToDefault();
            chartInstance.hideResetZoomButton();
        });
    }
    
    showResetZoomButton() {
        if (this.resetZoomBtnEl) this.resetZoomBtnEl.style.display = 'block';
    }
    
    hideResetZoomButton() {
        if (this.resetZoomBtnEl) this.resetZoomBtnEl.style.display = 'none';
    }
    
    resetZoomToDefault() {
        // Восстанавливаем вид как при первоначальной отрисовке (как в initializeFromData)
        const intervalMs = this.getIntervalMs(this.interval);
        const targetCandles = this.getDefaultVisibleCandles(this.interval);
        const dataTimeRange = Math.min(this.timeRange, targetCandles * intervalMs);
        this.visibleStartTime = this.endTime - dataTimeRange;
        const ratio = this.chartEndPositionRatio;
        this.visibleEndTime = this.endTime + dataTimeRange * (1 / ratio - 1);
        const visibleCandles = this.candles.filter(c => c.time >= this.visibleStartTime && c.time <= this.endTime);
        if (visibleCandles.length > 0) {
            const vHigh = Math.max(...visibleCandles.map(c => c.high));
            const vLow = Math.min(...visibleCandles.map(c => c.low));
            const vRange = vHigh - vLow || this.priceRange * 0.1;
            const pad = vRange * 0.1;
            this.visibleMinPrice = vLow - pad;
            this.visibleMaxPrice = vHigh + pad;
        } else {
            this.visibleMinPrice = this.minPrice;
            this.visibleMaxPrice = this.maxPrice;
        }
        this.zoomLevel = 1.0;
        this.axisZoomUsed = false;
        this.hideResetZoomButton();
        this.draw();
    }
    
    setupDrawingEvents() {
        // Mouse move handler for ruler mode (update second point on mouse move)
        this.canvas.addEventListener('mousemove', (e) => {
            const rect = this.canvas.getBoundingClientRect();
            const x = e.clientX - rect.left;
            const y = e.clientY - rect.top;
            
            // Масштабирование сдвигом: по времени — точка под курсором; по цене — центр видимого диапазона.
            if (this.isZoomDragging && this.zoomDragStartVisible) {
                const deltaX = x - this.zoomDragStartX;
                const deltaY = y - this.zoomDragStartY;
                const chartAreaHeight = this.chartHeight - this.volumeHeight;
                const normX = this.chartWidth > 0 ? (this.zoomDragStartX - this.padding.left) / this.chartWidth : 0.5;
                const pivotTime = this.zoomDragStartVisible.startTime + normX * (this.zoomDragStartVisible.endTime - this.zoomDragStartVisible.startTime);
                const pivotPrice = (this.zoomDragStartVisible.minPrice + this.zoomDragStartVisible.maxPrice) / 2;
                const timeMult = Math.max(0.05, Math.min(3, 1 - deltaX / 400));
                const priceMult = Math.max(0.05, Math.min(3, 1 + deltaY / 400));
                let newTimeRange = this.zoomDragStartTimeRange * timeMult;
                let newPriceRange = this.zoomDragStartPriceRange * priceMult;
                newTimeRange = Math.max(this.timeRange * 0.005, newTimeRange);
                newPriceRange = Math.max(this.priceRange * 0.005, newPriceRange);
                let newStartTime = pivotTime - newTimeRange * normX;
                let newEndTime = newStartTime + newTimeRange;
                let newMinPrice = pivotPrice - newPriceRange / 2;
                let newMaxPrice = pivotPrice + newPriceRange / 2;
                const oneViewW = this.timeRange * 0.5;
                if (newStartTime < this.startTime - oneViewW) { newStartTime = this.startTime - oneViewW; newEndTime = newStartTime + newTimeRange; }
                if (newEndTime > this.endTime + oneViewW) { newEndTime = this.endTime + oneViewW; newStartTime = newEndTime - newTimeRange; }
                this.visibleStartTime = newStartTime;
                this.visibleEndTime = newEndTime;
                this.visibleMinPrice = newMinPrice;
                this.visibleMaxPrice = newMaxPrice;
                this.axisZoomUsed = true;
                this.showResetZoomButton();
                this.draw();
                return;
            }
            // Handle panning (when no drawing tools are active). Shift — только по времени, Alt — только по цене, иначе — по обеим осям.
            if (this.isPanning && !this.drawingMode && !this.horizontalLineMode && 
                !this.rectangleMode && !this.rulerMode) {
                const deltaX = x - this.panStartX;
                const deltaY = y - this.panStartY;
                const timeRange = this.panStartVisibleEndTime - this.panStartVisibleStartTime;
                const priceRange = this.panStartVisibleMaxPrice - this.panStartVisibleMinPrice;
                const timeDelta = (this.chartWidth > 0) ? -(deltaX / this.chartWidth) * timeRange : 0;
                const priceDelta = (deltaY / (this.chartHeight - this.volumeHeight)) * priceRange;
                
                const panTime = !e.altKey;
                const panPrice = !e.shiftKey;
                
                let newStartTime = panTime ? this.panStartVisibleStartTime + timeDelta : this.panStartVisibleStartTime;
                let newEndTime = panTime ? this.panStartVisibleEndTime + timeDelta : this.panStartVisibleEndTime;
                let newMinPrice = panPrice ? this.panStartVisibleMinPrice + priceDelta : this.panStartVisibleMinPrice;
                let newMaxPrice = panPrice ? this.panStartVisibleMaxPrice + priceDelta : this.panStartVisibleMaxPrice;
                
                const maxTimeOver = timeRange;
                const maxPriceOver = priceRange;
                if (newStartTime < this.startTime - maxTimeOver) {
                    newStartTime = this.startTime - maxTimeOver;
                    newEndTime = newStartTime + timeRange;
                }
                if (newEndTime > this.endTime + maxTimeOver) {
                    newEndTime = this.endTime + maxTimeOver;
                    newStartTime = newEndTime - timeRange;
                }
                if (newMinPrice < this.minPrice - maxPriceOver) {
                    newMinPrice = this.minPrice - maxPriceOver;
                    newMaxPrice = newMinPrice + priceRange;
                }
                if (newMaxPrice > this.maxPrice + maxPriceOver) {
                    newMaxPrice = this.maxPrice + maxPriceOver;
                    newMinPrice = newMaxPrice - priceRange;
                }
                
                this.visibleStartTime = newStartTime;
                this.visibleEndTime = newEndTime;
                this.visibleMinPrice = newMinPrice;
                this.visibleMaxPrice = newMaxPrice;
                
                this.draw();
                return;
            }
            
            // Update ruler selection on mouse move (without dragging)
            if (this.rulerMode && this.currentRulerSelection) {
                // Constrain to chart area
                const chartAreaHeight = this.chartHeight - this.volumeHeight;
                const maxX = this.logicalWidth - this.padding.right;
                const maxY = this.padding.top + chartAreaHeight;
                
                this.currentRulerSelection.x2 = Math.max(this.padding.left, Math.min(maxX, x));
                this.currentRulerSelection.y2 = Math.max(this.padding.top, Math.min(maxY, y));
                this.draw();
                return;
            }
            
            // Preview for brush mode
            if (this.drawingMode && this.currentLine) {
                this.tempPoint = { x, y };
                this.draw();
                return;
            }
            
            // Preview for rectangle mode
            if (this.rectangleMode && this.currentRectangle) {
                this.tempPoint = { x, y };
                this.draw();
                return;
            }
        });
        
        // Mouse click handler
        this.canvas.addEventListener('click', (e) => {
            const rect = this.canvas.getBoundingClientRect();
            const x = e.clientX - rect.left;
            const y = e.clientY - rect.top;
            
            // Check if click is within chart area (excluding volume)
            const chartAreaHeight = this.chartHeight - this.volumeHeight;
            if (x < this.padding.left || x > this.logicalWidth - this.padding.right ||
                y < this.padding.top || y > this.padding.top + chartAreaHeight) {
                return;
            }
            
            // Handle ruler mode (two clicks: first sets start, second completes)
            if (this.rulerMode) {
                if (!this.currentRulerSelection) {
                    // First click - set first point
                    this.currentRulerSelection = { x1: x, y1: y, x2: x, y2: y };
                    this.draw();
                } else {
                    // Second click - complete the selection
                    // Constrain to chart area
                    const maxX = this.logicalWidth - this.padding.right;
                    const maxY = this.padding.top + chartAreaHeight;
                    
                    this.currentRulerSelection.x2 = Math.max(this.padding.left, Math.min(maxX, x));
                    this.currentRulerSelection.y2 = Math.max(this.padding.top, Math.min(maxY, y));
                    
                    const t1 = this.xToTime(this.currentRulerSelection.x1);
                    const p1 = this.yToPrice(this.currentRulerSelection.y1);
                    const t2 = this.xToTime(this.currentRulerSelection.x2);
                    const p2 = this.yToPrice(this.currentRulerSelection.y2);
                    const startTime = Math.min(t1, t2);
                    const endTime = Math.max(t1, t2);
                    const minPrice = Math.min(p1, p2);
                    const maxPrice = Math.max(p1, p2);
                    const summary = this.calculateRulerSummaryFromBounds(startTime, endTime, minPrice, maxPrice);
                    this.rulerSelections.push({
                        time1: t1, price1: p1, time2: t2, price2: p2,
                        summary: summary
                    });
                    this.currentRulerSelection = null;
                    this.draw();
                    this.setRulerMode(false);
                    document.querySelector('.tool-btn[title="Ruler"]')?.classList.remove('active');
                }
                return;
            }
            
            // Handle horizontal line mode (сохраняем в координатах графика: время, цена)
            if (this.horizontalLineMode) {
                this.horizontalLines.push({
                    time1: this.xToTime(x),
                    price: this.yToPrice(y)
                });
                this.draw();
                this.setHorizontalLineMode(false);
                document.querySelector('.tool-btn[title="Horizontal Line"]')?.classList.remove('active');
                return;
            }
            
            // Handle alert mode: прерывистый луч от точки клика до конца графика
            if (this.alertMode) {
                this.horizontalLines.push({
                    time1: this.xToTime(x),
                    price: this.yToPrice(y),
                    alert: true
                });
                this.draw();
                this.setAlertMode(false);
                document.querySelector('.tool-btn[title="Alert"]')?.classList.remove('active');
                return;
            }
            
            // Handle rectangle mode
            if (this.rectangleMode) {
                if (!this.currentRectangle) {
                    // First point - start of rectangle
                    this.currentRectangle = { x1: x, y1: y, x2: null, y2: null };
                    this.tempPoint = { x, y };
                    this.draw();
                } else {
                    // Second point - complete the rectangle (right bottom corner)
                    this.currentRectangle.x2 = x;
                    this.currentRectangle.y2 = y;
                    this.rectangles.push({
                        time1: this.xToTime(this.currentRectangle.x1),
                        price1: this.yToPrice(this.currentRectangle.y1),
                        time2: this.xToTime(this.currentRectangle.x2),
                        price2: this.yToPrice(this.currentRectangle.y2)
                    });
                    this.currentRectangle = null;
                    this.tempPoint = null;
                    this.draw();
                    this.setRectangleMode(false);
                    document.querySelector('.tool-btn[title="Rectangle"]')?.classList.remove('active');
                }
                return;
            }
            
            // Handle brush drawing mode
            if (this.drawingMode) {
                if (!this.currentLine) {
                    this.currentLine = { x1: x, y1: y, x2: null, y2: null };
                    this.tempPoint = { x, y };
                    this.draw();
                } else {
                    this.currentLine.x2 = x;
                    this.currentLine.y2 = y;
                    this.drawnLines.push({
                        time1: this.xToTime(this.currentLine.x1),
                        price1: this.yToPrice(this.currentLine.y1),
                        time2: this.xToTime(this.currentLine.x2),
                        price2: this.yToPrice(this.currentLine.y2)
                    });
                    this.currentLine = null;
                    this.tempPoint = null;
                    this.draw();
                    this.setDrawingMode(false);
                    document.querySelector('.tool-btn[title="Brush"]')?.classList.remove('active');
                }
                return;
            }
            
            // Выделение элемента по клику (вне режимов рисования) для удаления по Delete/Backspace
            const hit = this.hitTestDrawnElements(x, y);
            this.selectedDrawing = hit;
            this.canvas.focus();
            this.draw();
        });
        
        // Delete/Backspace — удалить выделенный элемент (на document, чтобы работало при любом фокусе)
        const onKeyDown = (e) => {
            if ((e.key !== 'Delete' && e.key !== 'Backspace') || !this.selectedDrawing) return;
            const el = document.activeElement;
            if (el && (el.tagName === 'INPUT' || el.tagName === 'TEXTAREA' || el.isContentEditable)) return;
            e.preventDefault();
            const s = this.selectedDrawing;
            if (s.type === 'line') this.drawnLines.splice(s.index, 1);
            else if (s.type === 'rect') this.rectangles.splice(s.index, 1);
            else if (s.type === 'ray') this.horizontalLines.splice(s.index, 1);
            else if (s.type === 'ruler') this.rulerSelections.splice(s.index, 1);
            this.selectedDrawing = null;
            this.draw();
        };
        document.addEventListener('keydown', onKeyDown);
        
        // Mouse down: в области осей (слева/снизу) — масштабирование по осям; в области графика — панорамирование
        this.canvas.addEventListener('mousedown', (e) => {
            if (!this.drawingMode && !this.horizontalLineMode && !this.alertMode &&
                !this.rectangleMode && !this.rulerMode) {
                const rect = this.canvas.getBoundingClientRect();
                const x = e.clientX - rect.left;
                const y = e.clientY - rect.top;
                if (x < 0 || x > this.logicalWidth || y < 0 || y > this.logicalHeight) return;
                const chartAreaHeight = this.chartHeight - this.volumeHeight;
                // Ось цены — справа (где подписи цен), ось времени — снизу (объём + подписи времени)
                const inPriceAxis = this.logicalWidth > 0 && x >= this.logicalWidth - this.padding.right;
                const inTimeAxis = this.chartHeight > 0 && y >= this.padding.top + chartAreaHeight;
                const inAxisArea = inPriceAxis || inTimeAxis;
                if (e.button === 0) {
                    if (inAxisArea) {
                        this.isZoomDragging = true;
                        this.zoomDragStartX = x;
                        this.zoomDragStartY = y;
                        this.zoomDragStartTimeRange = this.visibleEndTime - this.visibleStartTime;
                        this.zoomDragStartPriceRange = this.visibleMaxPrice - this.visibleMinPrice;
                        this.zoomDragStartVisible = {
                            startTime: this.visibleStartTime,
                            endTime: this.visibleEndTime,
                            minPrice: this.visibleMinPrice,
                            maxPrice: this.visibleMaxPrice
                        };
                        this.canvas.style.cursor = 'grabbing';
                    } else {
                        this.isPanning = true;
                        this.panStartX = x;
                        this.panStartY = y;
                        this.panStartVisibleStartTime = this.visibleStartTime;
                        this.panStartVisibleEndTime = this.visibleEndTime;
                        this.panStartVisibleMinPrice = this.visibleMinPrice;
                        this.panStartVisibleMaxPrice = this.visibleMaxPrice;
                        this.canvas.style.cursor = 'grabbing';
                    }
                } else if (e.button === 2) {
                    this.isPanning = true;
                    this.panStartX = x;
                    this.panStartY = y;
                    this.panStartVisibleStartTime = this.visibleStartTime;
                    this.panStartVisibleEndTime = this.visibleEndTime;
                    this.panStartVisibleMinPrice = this.visibleMinPrice;
                    this.panStartVisibleMaxPrice = this.visibleMaxPrice;
                    this.canvas.style.cursor = 'grabbing';
                }
            }
        });
        
        // Mouse up: отпускание кнопки завершает панорамирование и масштабирование
        this.canvas.addEventListener('mouseup', (e) => {
            if (e.button === 0) {
                this.isZoomDragging = false;
                this.isPanning = false;
                this.canvas.style.cursor = 'default';
            }
            if (e.button === 2 && this.isPanning) {
                this.isPanning = false;
                this.canvas.style.cursor = 'default';
            }
        });
        
        // Mouse leave handler to stop panning / zoom-by-drag if mouse leaves canvas
        this.canvas.addEventListener('mouseleave', (e) => {
            if (this.isPanning) {
                this.isPanning = false;
                this.canvas.style.cursor = 'default';
            }
            if (this.isZoomDragging) {
                this.isZoomDragging = false;
                this.canvas.style.cursor = 'default';
            }
        });
        
        // Правая кнопка мыши: отменить текущее рисование или удалить элемент при клике по линии/прямоугольнику/лучу
        this.canvas.addEventListener('contextmenu', (e) => {
            e.preventDefault();
            if (this.drawingMode && this.currentLine) {
                this.currentLine = null;
                this.tempPoint = null;
                this.draw();
                return;
            }
            if (this.rulerMode && this.currentRulerSelection) {
                this.currentRulerSelection = null;
                this.draw();
                return;
            }
            if (this.rectangleMode && this.currentRectangle) {
                this.currentRectangle = null;
                this.tempPoint = null;
                this.draw();
                return;
            }
            const rect = this.canvas.getBoundingClientRect();
            const x = e.clientX - rect.left;
            const y = e.clientY - rect.top;
            const hit = this.hitTestDrawnElements(x, y);
            if (hit) {
                if (hit.type === 'line') this.drawnLines.splice(hit.index, 1);
                else if (hit.type === 'rect') this.rectangles.splice(hit.index, 1);
                else if (hit.type === 'ray') this.horizontalLines.splice(hit.index, 1);
                else if (hit.type === 'ruler') this.rulerSelections.splice(hit.index, 1);
                this.selectedDrawing = null;
                this.draw();
            }
        });
        
        // Change cursor when in drawing mode or panning
        this.canvas.addEventListener('mousemove', (e) => {
            const rect = this.canvas.getBoundingClientRect();
            const x = e.clientX - rect.left;
            const y = e.clientY - rect.top;
            const isOnCanvas = x >= 0 && x <= this.logicalWidth && y >= 0 && y <= this.logicalHeight;
            
            if (this.drawingMode || this.horizontalLineMode || this.alertMode || this.rectangleMode || this.rulerMode) {
                this.canvas.style.cursor = 'crosshair';
            } else if (this.isZoomDragging) {
                this.canvas.style.cursor = 'grabbing';
            } else if (this.isPanning) {
                this.canvas.style.cursor = 'grabbing';
            } else if (isOnCanvas) {
                this.canvas.style.cursor = 'grab';
            } else {
                this.canvas.style.cursor = 'default';
            }
        });
    }
    
    setDrawingMode(enabled) {
        this.drawingMode = enabled;
        if (!enabled) {
            this.currentLine = null;
            this.tempPoint = null;
        }
        if (enabled) {
            this.horizontalLineMode = false;
            this.alertMode = false;
            this.rectangleMode = false;
            this.rulerMode = false;
            this.currentRectangle = null;
            this.currentRulerSelection = null;
        }
        this.canvas.style.cursor = (enabled || this.horizontalLineMode || this.alertMode || this.rectangleMode || this.rulerMode) ? 'crosshair' : 'default';
    }
    
    setHorizontalLineMode(enabled) {
        this.horizontalLineMode = enabled;
        if (enabled) {
            this.drawingMode = false;
            this.alertMode = false;
            this.rectangleMode = false;
            this.rulerMode = false;
            this.currentLine = null;
            this.currentRectangle = null;
            this.currentRulerSelection = null;
            this.tempPoint = null;
        }
        this.canvas.style.cursor = (enabled || this.drawingMode || this.alertMode || this.rectangleMode || this.rulerMode) ? 'crosshair' : 'default';
    }
    
    setAlertMode(enabled) {
        this.alertMode = enabled;
        if (enabled) {
            this.drawingMode = false;
            this.horizontalLineMode = false;
            this.rectangleMode = false;
            this.rulerMode = false;
            this.currentLine = null;
            this.currentRectangle = null;
            this.currentRulerSelection = null;
            this.tempPoint = null;
        }
        this.canvas.style.cursor = (enabled || this.drawingMode || this.horizontalLineMode || this.rectangleMode || this.rulerMode) ? 'crosshair' : 'default';
    }
    
    setRectangleMode(enabled) {
        this.rectangleMode = enabled;
        if (enabled) {
            this.drawingMode = false;
            this.horizontalLineMode = false;
            this.alertMode = false;
            this.rulerMode = false;
            this.currentLine = null;
            this.currentRectangle = null;
            this.currentRulerSelection = null;
            this.tempPoint = null;
        }
        this.canvas.style.cursor = (enabled || this.drawingMode || this.horizontalLineMode || this.alertMode || this.rulerMode) ? 'crosshair' : 'default';
    }
    
    setRulerMode(enabled) {
        this.rulerMode = enabled;
        if (enabled) {
            this.drawingMode = false;
            this.horizontalLineMode = false;
            this.alertMode = false;
            this.rectangleMode = false;
            this.currentLine = null;
            this.currentRectangle = null;
            this.currentRulerSelection = null;
            this.tempPoint = null;
        }
        this.canvas.style.cursor = (enabled || this.drawingMode || this.horizontalLineMode || this.alertMode || this.rectangleMode) ? 'crosshair' : 'default';
    }
    
    calculateRulerSummaryFromBounds(startTime, endTime, minPrice, maxPrice) {
        const selectedCandles = this.candles.filter(candle => {
            if (candle.time < startTime || candle.time > endTime) return false;
            return !(candle.low > maxPrice || candle.high < minPrice);
        });
        if (selectedCandles.length === 0) {
            return { count: 0, percentChange: '0%', timePeriod: '0н 0ч', bars: 0 };
        }
        const sortedCandles = [...selectedCandles].sort((a, b) => a.time - b.time);
        const firstCandle = sortedCandles[0];
        const lastCandle = sortedCandles[sortedCandles.length - 1];
        const firstPrice = firstCandle.open;
        const lastPrice = lastCandle.close;
        const percentChange = ((lastPrice - firstPrice) / firstPrice) * 100;
        const percentChangeStr = (percentChange >= 0 ? '+' : '') + percentChange.toFixed(2) + '%';
        const timeDiff = endTime - startTime;
        const weeks = Math.floor(timeDiff / (7 * 24 * 60 * 60 * 1000));
        const hours = Math.floor((timeDiff % (7 * 24 * 60 * 60 * 1000)) / (60 * 60 * 1000));
        const timePeriodStr = `${weeks}н ${hours}ч`;
        return { count: selectedCandles.length, percentChange: percentChangeStr, timePeriod: timePeriodStr, bars: selectedCandles.length };
    }
    
    calculateRulerSummary(selection) {
        // Convert screen coordinates to price and time ranges
        const x1 = Math.min(selection.x1, selection.x2);
        const x2 = Math.max(selection.x1, selection.x2);
        const y1 = Math.min(selection.y1, selection.y2);
        const y2 = Math.max(selection.y1, selection.y2);
        
        // Convert Y coordinates to prices
        const price1 = this.yToPrice(y2); // Top Y = higher price
        const price2 = this.yToPrice(y1); // Bottom Y = lower price
        const minPrice = Math.min(price1, price2);
        const maxPrice = Math.max(price1, price2);
        
        // Convert X coordinates to times
        const time1 = this.xToTime(x1);
        const time2 = this.xToTime(x2);
        const startTime = Math.min(time1, time2);
        const endTime = Math.max(time1, time2);
        
        return this.calculateRulerSummaryFromBounds(startTime, endTime, minPrice, maxPrice);
    }
    
    yToPrice(y) {
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const visiblePriceRange = this.visibleMaxPrice - this.visibleMinPrice;
        const normalized = (this.padding.top + chartAreaHeight - y) / chartAreaHeight;
        return this.visibleMinPrice + normalized * visiblePriceRange;
    }
    
    xToTime(x) {
        const visibleTimeRange = this.visibleEndTime - this.visibleStartTime;
        if (this.chartWidth <= 0) return this.visibleStartTime;
        let normalized = (x - this.padding.left) / this.chartWidth;
        normalized = Math.max(0, Math.min(1, normalized));
        return this.visibleStartTime + normalized * visibleTimeRange;
    }
    
    distanceToSegment(px, py, x1, y1, x2, y2) {
        const dx = x2 - x1;
        const dy = y2 - y1;
        const len = Math.hypot(dx, dy) || 1e-6;
        const t = Math.max(0, Math.min(1, ((px - x1) * dx + (py - y1) * dy) / (len * len)));
        const nx = x1 + t * dx;
        const ny = y1 + t * dy;
        return Math.hypot(px - nx, py - ny);
    }
    
    hitTestDrawnElements(px, py) {
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const maxX = this.logicalWidth - this.padding.right;
        const threshold = 10;
        for (let i = this.rectangles.length - 1; i >= 0; i--) {
            const rect = this.rectangles[i];
            let x1, y1, x2, y2;
            if (rect.time1 != null && rect.price1 != null) {
                x1 = this.timeToX(rect.time1);
                y1 = this.priceToY(rect.price1);
                x2 = this.timeToX(rect.time2);
                y2 = this.priceToY(rect.price2);
            } else {
                x1 = rect.x1; y1 = rect.y1; x2 = rect.x2; y2 = rect.y2;
            }
            const x = Math.min(x1, x2) - threshold;
            const y = Math.min(y1, y2) - threshold;
            const w = Math.abs(x2 - x1) + 2 * threshold;
            const h = Math.abs(y2 - y1) + 2 * threshold;
            if (px >= x && px <= x + w && py >= y && py <= y + h) return { type: 'rect', index: i };
        }
        for (let i = this.horizontalLines.length - 1; i >= 0; i--) {
            const line = this.horizontalLines[i];
            let x1, y1, x2, y2;
            if (line.time1 != null && line.price != null) {
                x1 = this.timeToX(line.time1);
                y1 = this.priceToY(line.price);
                x2 = maxX;
                y2 = y1;
            } else {
                x1 = line.x1; y1 = line.y1; x2 = line.x2; y2 = line.y2;
            }
            if (this.distanceToSegment(px, py, x1, y1, x2, y2) <= threshold && px >= Math.min(x1, x2) - threshold) return { type: 'ray', index: i };
        }
        for (let i = this.drawnLines.length - 1; i >= 0; i--) {
            const line = this.drawnLines[i];
            let x1, y1, x2, y2;
            if (line.time1 != null && line.price1 != null) {
                x1 = this.timeToX(line.time1);
                y1 = this.priceToY(line.price1);
                x2 = this.timeToX(line.time2);
                y2 = this.priceToY(line.price2);
            } else {
                x1 = line.x1; y1 = line.y1; x2 = line.x2; y2 = line.y2;
            }
            if (this.distanceToSegment(px, py, x1, y1, x2, y2) <= threshold) return { type: 'line', index: i };
        }
        for (let i = this.rulerSelections.length - 1; i >= 0; i--) {
            const sel = this.rulerSelections[i];
            let x1, y1, x2, y2;
            if (sel.time1 != null && sel.price1 != null) {
                x1 = this.timeToX(sel.time1);
                y1 = this.priceToY(sel.price1);
                x2 = this.timeToX(sel.time2);
                y2 = this.priceToY(sel.price2);
            } else {
                x1 = sel.x1; y1 = sel.y1; x2 = sel.x2; y2 = sel.y2;
            }
            const x = Math.min(x1, x2) - threshold;
            const y = Math.min(y1, y2) - threshold;
            const w = Math.abs(x2 - x1) + 2 * threshold;
            const h = Math.abs(y2 - y1) + 2 * threshold;
            if (px >= x && px <= x + w && py >= y && py <= y + h) return { type: 'ruler', index: i };
        }
        return null;
    }
    
    clearDrawnLines() {
        this.drawnLines = [];
        this.horizontalLines = [];
        this.rectangles = [];
        this.rulerSelections = [];
        this.currentLine = null;
        this.currentRectangle = null;
        this.currentRulerSelection = null;
        this.tempPoint = null;
        this.draw();
    }
    
    resize() {
        const container = this.canvas.parentElement;
        if (!container) {
            console.error('Canvas container not found!');
            return;
        }
        
        const rect = container.getBoundingClientRect();
        const width = Math.max(1, rect.width);
        const height = Math.max(1, rect.height);
        
        this.dpr = Math.min(window.devicePixelRatio || 1, 2);
        this.logicalWidth = width;
        this.logicalHeight = height;
        this.canvas.width = width * this.dpr;
        this.canvas.height = height * this.dpr;
        this.canvas.style.width = width + 'px';
        this.canvas.style.height = height + 'px';
        this.ctx.setTransform(this.dpr, 0, 0, this.dpr, 0, 0);
        
        const oldChartWidth = this.chartWidth;
        this.chartWidth = width - this.padding.left - this.padding.right;
        this.chartHeight = height - this.padding.top - this.padding.bottom;
        
        // Update horizontal lines to extend to new right edge
        if (oldChartWidth > 0 && this.chartWidth !== oldChartWidth) {
            const rightEdge = this.logicalWidth - this.padding.right;
            this.horizontalLines.forEach(line => {
                if (line.x2 != null) line.x2 = rightEdge;
            });
        }
        
        // Only draw if we have valid dimensions and data
        if (this.chartWidth > 0 && this.chartHeight > 0 && this.candles.length > 0) {
            this.draw();
        }
    }
    
    async loadBinanceData(symbol = 'BTCUSDT', interval = '1d', limit = 500) {
        try {
            // First, load historical data via REST API for initial display
            console.log(`Loading ${limit} historical candles for ${symbol} with interval ${interval}...`);
            
            // Binance REST API endpoint for klines (candlestick data)
            const url = `https://api.binance.com/api/v3/klines?symbol=${symbol}&interval=${interval}&limit=${limit}`;
            
            const response = await fetch(url);
            if (!response.ok) {
                throw new Error(`HTTP error! status: ${response.status}`);
            }
            
            const klines = await response.json();
            
            // Convert Binance klines format to our format
            // Binance format: [openTime, open, high, low, close, volume, closeTime, ...]
            this.candles = klines.map(kline => ({
                time: kline[0], // Open time in milliseconds
                open: parseFloat(kline[1]),
                high: parseFloat(kline[2]),
                low: parseFloat(kline[3]),
                close: parseFloat(kline[4])
            }));
            
            // Extract volume data
            this.volumeData = klines.map(kline => parseFloat(kline[5])); // Volume
            
            if (this.candles.length === 0) {
                console.error('No candles data received from Binance!');
                return;
            }
            
            // Store symbol and interval
            this.symbol = symbol.toUpperCase();
            this.interval = interval;
            // Биржа — источник данных (отображается в шапке)
            this.exchangeName = 'Binance';
            
            // Initialize chart with historical data
            this.initializeFromData();
            
            // Connect to WebSocket for real-time updates
            this.connectWebSocket();
            
        } catch (error) {
            console.error('Error loading Binance data:', error);
            // Fallback to sample data if API fails
            console.log('Falling back to sample data...');
            this.exchangeName = 'Демо';
            this.candles = this.generateSampleData();
            this.volumeData = this.generateVolumeData();
            this.initializeFromData();
        }
    }
    
    connectWebSocket() {
        // Close existing connection if any
        if (this.ws) {
            this.ws.close();
        }
        
        // Binance WebSocket stream URL
        // Format: wss://stream.binance.com:9443/ws/{symbol}@kline_{interval}
        const symbolLower = this.symbol.toLowerCase();
        const wsUrl = `wss://stream.binance.com:9443/ws/${symbolLower}@kline_${this.interval}`;
        
        console.log(`Connecting to WebSocket: ${wsUrl}`);
        
        try {
            this.ws = new WebSocket(wsUrl);
            
            this.ws.onopen = () => {
                console.log('WebSocket connected to Binance');
                this.wsReconnectAttempts = 0;
            };
            
            this.ws.onmessage = (event) => {
                try {
                    const data = JSON.parse(event.data);
                    this.handleWebSocketMessage(data);
                } catch (error) {
                    console.error('Error parsing WebSocket message:', error);
                }
            };
            
            this.ws.onerror = (error) => {
                console.error('WebSocket error:', error);
            };
            
            this.ws.onclose = () => {
                console.log('WebSocket connection closed');
                // Attempt to reconnect
                this.reconnectWebSocket();
            };
        } catch (error) {
            console.error('Error creating WebSocket connection:', error);
            this.reconnectWebSocket();
        }
    }
    
    reconnectWebSocket() {
        if (this.wsReconnectAttempts >= this.maxReconnectAttempts) {
            console.error('Max reconnection attempts reached. WebSocket will not reconnect.');
            return;
        }
        
        this.wsReconnectAttempts++;
        const delay = Math.min(1000 * Math.pow(2, this.wsReconnectAttempts), 30000); // Exponential backoff, max 30s
        
        console.log(`Attempting to reconnect WebSocket in ${delay}ms (attempt ${this.wsReconnectAttempts}/${this.maxReconnectAttempts})...`);
        
        setTimeout(() => {
            this.connectWebSocket();
        }, delay);
    }
    
    handleWebSocketMessage(data) {
        // Binance kline WebSocket message format:
        // {
        //   "e": "kline",
        //   "E": 123456789,  // Event time
        //   "s": "BTCUSDT", // Symbol
        //   "k": {
        //     "t": 123400000, // Kline start time
        //     "T": 123400000, // Kline close time
        //     "s": "BTCUSDT", // Symbol
        //     "i": "1h",     // Interval
        //     "f": 100,       // First trade ID
        //     "L": 200,       // Last trade ID
        //     "o": "0.0010",  // Open price
        //     "c": "0.0020",  // Close price
        //     "h": "0.0025",  // High price
        //     "l": "0.0005",  // Low price
        //     "v": "1000",    // Volume
        //     "n": 100,       // Number of trades
        //     "x": false,     // Is this kline closed?
        //     "q": "1.0000",  // Quote asset volume
        //     "V": "500",     // Taker buy base asset volume
        //     "Q": "0.500",   // Taker buy quote asset volume
        //     "B": "123456"   // Ignore
        //   }
        // }
        
        if (data.e === 'kline' && data.k) {
            const kline = data.k;
            const candleTime = kline.t; // Kline start time
            const isClosed = kline.x; // Is this kline closed?
            
            // Find existing candle with this time
            const candleIndex = this.candles.findIndex(c => c.time === candleTime);
            
            const candleData = {
                time: candleTime,
                open: parseFloat(kline.o),
                high: parseFloat(kline.h),
                low: parseFloat(kline.l),
                close: parseFloat(kline.c)
            };
            
            const volume = parseFloat(kline.v);
            
            if (candleIndex >= 0) {
                // Update existing candle
                this.candles[candleIndex] = candleData;
                this.volumeData[candleIndex] = volume;
            } else {
                // New candle (shouldn't happen often, but handle it)
                // Insert in correct chronological order
                let insertIndex = this.candles.length;
                for (let i = 0; i < this.candles.length; i++) {
                    if (this.candles[i].time > candleTime) {
                        insertIndex = i;
                        break;
                    }
                }
                this.candles.splice(insertIndex, 0, candleData);
                this.volumeData.splice(insertIndex, 0, volume);
                
                // Update time range if needed
                if (candleTime < this.startTime) {
                    this.startTime = candleTime;
                }
                if (candleTime > this.endTime) {
                    this.endTime = candleTime;
                }
                this.timeRange = this.endTime - this.startTime;
            }
            
            // If candle is closed, update price range and redraw
            if (isClosed) {
                // Recalculate price range
                const allPrices = this.candles.flatMap(c => [c.high, c.low]);
                const newMinPrice = Math.min(...allPrices);
                const newMaxPrice = Math.max(...allPrices);
                const newPriceRange = newMaxPrice - newMinPrice;
                
                // Add padding
                const pricePadding = newPriceRange * 0.05;
                this.minPrice = newMinPrice - pricePadding;
                this.maxPrice = newMaxPrice + pricePadding;
                this.priceRange = this.maxPrice - this.minPrice;
                
                // Update price levels
                this.updatePriceLevels();
            }
            
            this.updateTopBarMetrics();
            // Redraw chart
            this.draw();
        }
    }
    
    disconnectWebSocket() {
        if (this.ws) {
            this.ws.close();
            this.ws = null;
            console.log('WebSocket disconnected');
        }
    }
    
    async changeTimeframe(newInterval) {
        console.log(`Changing timeframe to ${newInterval}`);
        
        // Disconnect current WebSocket
        this.disconnectWebSocket();
        
        // Clear current data
        this.candles = [];
        this.volumeData = [];
        
        // Update interval
        this.interval = newInterval;
        
        // Reload data with new interval
        await this.loadBinanceData(this.symbol, newInterval, 500);
    }
    
    updatePriceLevels() {
        // Calculate key price levels (support/resistance levels)
        const priceStep = this.priceRange / 5;
        this.priceLevels = [];
        
        // Add some key levels
        for (let i = 0; i <= 5; i++) {
            const price = this.minPrice + i * priceStep;
            const isHighlight = i === 2 || i === 3; // Highlight middle levels
            this.priceLevels.push({
                price: price,
                label: this.formatPrice(price),
                dashed: true,
                highlight: isHighlight,
                current: false
            });
        }
    }
    
    updateTopBarMetrics() {
        const el = id => document.getElementById(id);
        const exchangeEl = el('exchangeName');
        if (exchangeEl) exchangeEl.textContent = this.exchangeName || '—';
        
        if (!this.candles || this.candles.length === 0) {
            if (el('metricPriceChangeValue')) el('metricPriceChangeValue').textContent = '—';
            if (el('metricPriceRangeValue')) el('metricPriceRangeValue').textContent = '—';
            if (el('metricVolatilityValue')) el('metricVolatilityValue').textContent = '—';
            if (el('metricVolumeValue')) el('metricVolumeValue').textContent = '—';
            return;
        }
        
        const first = this.candles[0];
        const last = this.candles[this.candles.length - 1];
        
        // Изменение цены %: (последняя закрытие - первая открытие) / первая открытие * 100
        const priceChangePct = first.open !== 0
            ? ((last.close - first.open) / first.open) * 100
            : 0;
        const priceChangeEl = el('metricPriceChangeValue');
        const priceChangeBox = el('metricPriceChange');
        if (priceChangeEl) {
            priceChangeEl.textContent = priceChangePct >= 0
                ? '+' + priceChangePct.toFixed(2) + '%'
                : priceChangePct.toFixed(2) + '%';
        }
        if (priceChangeBox) {
            priceChangeBox.classList.remove('metric-green', 'metric-red');
            priceChangeBox.classList.add(priceChangePct >= 0 ? 'metric-green' : 'metric-red');
        }
        
        // Ренж цены %: (макс High - мин Low) по всем свечам / мин Low * 100
        const maxHigh = Math.max(...this.candles.map(c => c.high));
        const minLow = Math.min(...this.candles.map(c => c.low));
        const priceRangePct = minLow !== 0 ? ((maxHigh - minLow) / minLow) * 100 : 0;
        if (el('metricPriceRangeValue')) {
            el('metricPriceRangeValue').textContent = priceRangePct.toFixed(2) + '%';
        }
        const rangeBox = el('metricPriceRange');
        if (rangeBox) {
            rangeBox.classList.remove('metric-green', 'metric-red');
            rangeBox.classList.add(priceRangePct >= 0 ? 'metric-green' : 'metric-red');
        }
        
        // Волатильность: среднее (high - low) / close * 100 по всем свечам
        let volatilitySum = 0;
        let volCount = 0;
        this.candles.forEach(c => {
            if (c.close > 0) {
                volatilitySum += ((c.high - c.low) / c.close) * 100;
                volCount++;
            }
        });
        const volatility = volCount > 0 ? volatilitySum / volCount : 0;
        if (el('metricVolatilityValue')) el('metricVolatilityValue').textContent = volatility.toFixed(2) + '%';
        
        // Объём: сумма объёма видимых/всех свечей, формат 27M, 1.2K
        const totalVol = (this.volumeData && this.volumeData.length) ? this.volumeData.reduce((a, b) => a + b, 0) : 0;
        let volStr = '—';
        if (totalVol >= 1e9) volStr = (totalVol / 1e9).toFixed(1) + 'B';
        else if (totalVol >= 1e6) volStr = (totalVol / 1e6).toFixed(0) + 'M';
        else if (totalVol >= 1e3) volStr = (totalVol / 1e3).toFixed(1) + 'K';
        else if (totalVol > 0) volStr = totalVol.toFixed(0);
        if (el('metricVolumeValue')) el('metricVolumeValue').textContent = volStr;
    }
    
    getIntervalMs(interval) {
        const m = (interval || this.interval || '1d').toString().toLowerCase().match(/^(\d+)(m|h|d|w)$/);
        if (!m) return 24 * 60 * 60 * 1000;
        const n = parseInt(m[1], 10);
        const u = m[2];
        if (u === 'm') return n * 60 * 1000;
        if (u === 'h') return n * 60 * 60 * 1000;
        if (u === 'd') return n * 24 * 60 * 60 * 1000;
        if (u === 'w') return n * 7 * 24 * 60 * 60 * 1000;
        return 24 * 60 * 60 * 1000;
    }
    
    getDefaultVisibleCandles(interval) {
        const s = (interval || this.interval || '1d').toString().toLowerCase();
        if (s === '1m' || s === '3m') return 45;
        if (s === '5m') return 55;
        if (s === '15m' || s === '30m') return 70;
        if (s === '1h' || s === '2h') return 85;
        if (s === '4h') return 100;
        return 120;
    }
    
    initializeFromData() {
        if (this.candles.length === 0) {
            console.error('No candles data to initialize!');
            return;
        }
        
        // Calculate price range from actual data
        const allPrices = this.candles.flatMap(c => [c.high, c.low]);
        this.minPrice = Math.min(...allPrices);
        this.maxPrice = Math.max(...allPrices);
        this.priceRange = this.maxPrice - this.minPrice;
        
        // Add some padding to price range (5% on each side)
        const pricePadding = this.priceRange * 0.05;
        this.minPrice -= pricePadding;
        this.maxPrice += pricePadding;
        this.priceRange = this.maxPrice - this.minPrice;
        
        // Update price levels
        this.updatePriceLevels();
        
        // Time range
        this.startTime = this.candles[0].time;
        this.endTime = this.candles[this.candles.length - 1].time;
        this.timeRange = this.endTime - this.startTime;
        
        // Чем меньше таймфрейм — показываем меньше свечей по умолчанию. Окончание графика смещаем на 2/3 ширины (справа пусто).
        const intervalMs = this.getIntervalMs(this.interval);
        const targetCandles = this.getDefaultVisibleCandles(this.interval);
        const dataTimeRange = Math.min(this.timeRange, targetCandles * intervalMs);
        this.visibleStartTime = this.endTime - dataTimeRange;
        const ratio = this.chartEndPositionRatio;
        this.visibleEndTime = this.endTime + dataTimeRange * (1 / ratio - 1);
        // Растягиваем по вертикали: видимый диапазон цен — по свечам в видимом интервале времени (с отступом)
        const visibleCandles = this.candles.filter(c => c.time >= this.visibleStartTime && c.time <= this.endTime);
        if (visibleCandles.length > 0) {
            const vHigh = Math.max(...visibleCandles.map(c => c.high));
            const vLow = Math.min(...visibleCandles.map(c => c.low));
            const vRange = vHigh - vLow || this.priceRange * 0.1;
            const pad = vRange * 0.1;
            this.visibleMinPrice = vLow - pad;
            this.visibleMaxPrice = vHigh + pad;
        } else {
            this.visibleMinPrice = this.minPrice;
            this.visibleMaxPrice = this.maxPrice;
        }
        
        this.updateTopBarMetrics();
        
        // Initial resize and draw
        this.resize();
    }
    
    generateSampleData() {
        const data = [];
        // Start from Feb 3, 2026 based on image
        const baseTime = new Date('2026-02-03T00:00:00').getTime();
        // Generate 3 months of hourly data (about 90 days = 2160 hours)
        const hours = 24 * 90; // ~90 days for panning
        
        // Simulate price movement with cycles and trends
        let price = 0.001800;
        
        for (let i = 0; i < hours; i++) {
            const time = baseTime + i * 60 * 60 * 1000;
            const volatility = 0.00008;
            
            // Simulate cyclical price movement with multiple cycles
            const dayProgress = i / 24;
            const cycle1 = Math.sin(dayProgress * 2 * Math.PI / 30) * 0.0002; // ~30 day cycle
            const cycle2 = Math.sin(dayProgress * 2 * Math.PI / 7) * 0.0001; // ~7 day cycle
            const trend = -0.00001 * dayProgress; // Slight overall downward trend
            
            // Add some spikes and dips at specific intervals
            let spike = 0;
            if (i % 500 < 20) {
                // Periodic spikes
                spike = 0.0002 * (1 - (i % 500) / 20);
            } else if (i % 700 < 30) {
                // Periodic dips
                spike = -0.00015 * (1 - (i % 700) / 30);
            }
            
            const open = price;
            const change = (Math.random() - 0.5) * volatility + trend + cycle1 + cycle2 + spike;
            const close = Math.max(this.minPrice, Math.min(this.maxPrice, open + change));
            const high = Math.max(open, close) + Math.random() * volatility * 0.6;
            const low = Math.min(open, close) - Math.random() * volatility * 0.6;
            
            price = close;
            
            data.push({
                time,
                open: Math.max(this.minPrice, Math.min(this.maxPrice, open)),
                high: Math.max(this.minPrice, Math.min(this.maxPrice, high)),
                low: Math.max(this.minPrice, Math.min(this.maxPrice, low)),
                close: Math.max(this.minPrice, Math.min(this.maxPrice, close))
            });
        }
        
        return data;
    }
    
    generateVolumeData() {
        return this.candles.map(() => Math.random() * 5000000 + 1000000);
    }
    
    priceToY(price) {
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const visiblePriceRange = this.visibleMaxPrice - this.visibleMinPrice;
        const normalized = (price - this.visibleMinPrice) / visiblePriceRange;
        // Chart area excludes volume at bottom
        return this.padding.top + chartAreaHeight - (normalized * chartAreaHeight);
    }
    
    timeToX(time) {
        const visibleTimeRange = this.visibleEndTime - this.visibleStartTime;
        if (visibleTimeRange <= 0) return this.padding.left;
        const normalized = (time - this.visibleStartTime) / visibleTimeRange;
        return this.padding.left + (normalized * this.chartWidth);
    }
    
    formatPrice(price) {
        // Format price based on its magnitude
        if (price >= 1) {
            return price.toFixed(2);
        } else if (price >= 0.01) {
            return price.toFixed(4);
        } else if (price >= 0.0001) {
            return price.toFixed(6);
        } else {
            return price.toFixed(8);
        }
    }
    
    formatTime(time) {
        const date = new Date(time);
        const day = date.getDate();
        const month = date.toLocaleString('ru', { month: 'short' });
        const year = date.getFullYear().toString().slice(-2);
        const hours = date.getHours().toString().padStart(2, '0');
        const minutes = date.getMinutes().toString().padStart(2, '0');
        const seconds = date.getSeconds().toString().padStart(2, '0');
        
        // Format similar to image: "08 февр. '26 11:00:00" for specific times
        // Or just day number for most labels
        if (date.getHours() === 11 && date.getMinutes() === 0 && date.getSeconds() === 0) {
            return `${day} ${month} '${year} ${hours}:${minutes}:${seconds}`;
        }
        if (date.getHours() === 0 && date.getMinutes() === 0) {
            return day.toString();
        }
        return `${hours}:${minutes}`;
    }
    
    drawGrid() {
        // Dashed grid lines
        this.ctx.setLineDash([3, 3]);
        this.ctx.strokeStyle = '#444';
        this.ctx.lineWidth = 1;
        
        // Chart area height (excluding volume) - exact boundaries
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = this.padding.left;
        const minY = this.padding.top;
        const maxX = this.logicalWidth - this.padding.right;
        const maxY = this.padding.top + chartAreaHeight;
        
        // Horizontal grid lines (price levels) - based on visible range
        const visiblePriceRange = this.visibleMaxPrice - this.visibleMinPrice;
        const numPriceLines = 5;
        const priceStep = visiblePriceRange / (numPriceLines - 1);
        
        for (let i = 0; i < numPriceLines; i++) {
            const price = this.visibleMinPrice + i * priceStep;
            const y = this.priceToY(price);
            // Only draw if within bounds
            if (y >= minY && y <= maxY) {
                this.ctx.beginPath();
                this.ctx.moveTo(minX, y);
                this.ctx.lineTo(maxX, y);
                this.ctx.stroke();
            }
        }
        
        // Vertical grid lines (time) - based on visible range
        const visibleTimeRange = this.visibleEndTime - this.visibleStartTime;
        const numTimeLines = 12;
        const timeStep = visibleTimeRange / numTimeLines;
        
        for (let i = 0; i <= numTimeLines; i++) {
            const time = this.visibleStartTime + i * timeStep;
            const x = this.timeToX(time);
            // Only draw if within bounds
            if (x >= minX && x <= maxX) {
                this.ctx.beginPath();
                this.ctx.moveTo(x, minY);
                this.ctx.lineTo(x, maxY);
                this.ctx.stroke();
            }
        }
        
        this.ctx.setLineDash([]);
    }
    
    drawPriceLevels() {
        // Chart area bounds
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = this.padding.left;
        const minY = this.padding.top;
        const maxX = this.logicalWidth - this.padding.right;
        const maxY = this.padding.top + chartAreaHeight;
        
        this.priceLevels.forEach(level => {
            const y = this.priceToY(level.price);
            
            // Only draw if within chart bounds (between axes)
            if (y < minY || y > maxY) return;
            
            if (level.dashed) {
                this.ctx.setLineDash([5, 5]);
                this.ctx.strokeStyle = level.highlight ? '#fff' : '#888';
                this.ctx.lineWidth = level.highlight ? 1.5 : 1;
            } else {
                this.ctx.setLineDash([]);
                this.ctx.strokeStyle = '#888';
                this.ctx.lineWidth = 1;
            }
            
            this.ctx.beginPath();
            this.ctx.moveTo(minX, y);
            this.ctx.lineTo(maxX, y);
            this.ctx.stroke();
            
            // Draw label
            if (level.highlight || level.current) {
                this.ctx.fillStyle = '#fff';
                this.ctx.font = '11px sans-serif';
                const textWidth = this.ctx.measureText(level.label).width;
                this.ctx.fillRect(this.logicalWidth - this.padding.right + 5, y - 9, textWidth + 6, 18);
                this.ctx.fillStyle = '#000';
                this.ctx.fillText(level.label, this.logicalWidth - this.padding.right + 8, y + 4);
            } else {
                this.ctx.fillStyle = '#999';
                this.ctx.font = '11px sans-serif';
                this.ctx.fillText(level.label, this.logicalWidth - this.padding.right + 5, y + 4);
            }
        });
        
        this.ctx.setLineDash([]);
    }
    
    drawCandles() {
        if (!this.candles || this.candles.length === 0) {
            console.warn('No candles to draw');
            return;
        }
        
        // Filter candles that are visible in current zoom range
        const visibleCandles = this.candles.filter(candle => {
            return candle.time >= this.visibleStartTime && candle.time <= this.visibleEndTime;
        });
        
        if (visibleCandles.length === 0) return;
        
        const visibleTimeRange = this.visibleEndTime - this.visibleStartTime;
        const intervalMs = this.getIntervalMs(this.interval);
        const candleWidth = visibleTimeRange > 0
            ? Math.max(1, (this.chartWidth * intervalMs / visibleTimeRange) * 0.7)
            : Math.max(1, this.chartWidth / visibleCandles.length * 0.7);
        const wickWidth = 1;
        
        // Chart area bounds for clipping
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = this.padding.left;
        const minY = this.padding.top;
        const maxX = this.logicalWidth - this.padding.right;
        const maxY = this.padding.top + chartAreaHeight;
        
        visibleCandles.forEach((candle, index) => {
            if (!candle || !candle.time) return;
            
            const x = this.timeToX(candle.time) - candleWidth / 2;
            let openY = this.priceToY(candle.open);
            let closeY = this.priceToY(candle.close);
            let highY = this.priceToY(candle.high);
            let lowY = this.priceToY(candle.low);
            
            // Clip Y coordinates to chart bounds (between axes)
            highY = Math.max(minY, Math.min(maxY, highY));
            lowY = Math.max(minY, Math.min(maxY, lowY));
            openY = Math.max(minY, Math.min(maxY, openY));
            closeY = Math.max(minY, Math.min(maxY, closeY));
            
            // Skip if candle is completely outside X bounds
            if (x + candleWidth < minX || x > maxX) {
                return;
            }
            
            // Skip if coordinates are invalid
            if (isNaN(x) || isNaN(openY) || isNaN(closeY) || isNaN(highY) || isNaN(lowY)) {
                return;
            }
            
            const isGreen = candle.close >= candle.open;
            const color = isGreen ? '#26a69a' : '#ef5350';
            
            // Clip candle X position to bounds
            const clippedX = Math.max(minX, Math.min(maxX - candleWidth, x));
            const clippedWidth = Math.min(candleWidth, maxX - clippedX);
            
            // Draw wick (thin vertical line) - only if visible
            if (clippedX + clippedWidth / 2 >= minX && clippedX + clippedWidth / 2 <= maxX) {
                this.ctx.strokeStyle = color;
                this.ctx.lineWidth = wickWidth;
                this.ctx.beginPath();
                this.ctx.moveTo(clippedX + clippedWidth / 2, highY);
                this.ctx.lineTo(clippedX + clippedWidth / 2, lowY);
                this.ctx.stroke();
            }
            
            // Draw body - clip to bounds
            const bodyTop = Math.min(openY, closeY);
            const bodyHeight = Math.max(1, Math.abs(closeY - openY));
            
            if (bodyTop < maxY && bodyTop + bodyHeight > minY) {
                // Clip body to bounds
                const clippedBodyTop = Math.max(minY, bodyTop);
                const clippedBodyHeight = Math.min(maxY, bodyTop + bodyHeight) - clippedBodyTop;
                
                // Fill body
                this.ctx.fillStyle = color;
                this.ctx.fillRect(clippedX, clippedBodyTop, clippedWidth, clippedBodyHeight);
                
                // Draw body border
                this.ctx.strokeStyle = color;
                this.ctx.lineWidth = 0.5;
                this.ctx.strokeRect(clippedX, clippedBodyTop, clippedWidth, clippedBodyHeight);
            }
        });
    }
    
    drawVolume() {
        if (!this.volumeData || this.volumeData.length === 0 || !this.candles || this.candles.length === 0) {
            return;
        }
        
        // Filter candles that are visible in current zoom range
        const visibleCandles = this.candles.filter(candle => {
            return candle.time >= this.visibleStartTime && candle.time <= this.visibleEndTime;
        });
        
        if (visibleCandles.length === 0) return;
        
        // Get volumes for visible candles
        const visibleVolumes = visibleCandles.map(candle => {
            const candleIndex = this.candles.findIndex(c => c.time === candle.time);
            return this.volumeData[candleIndex] || 0;
        });
        
        const maxVolume = Math.max(...visibleVolumes);
        if (maxVolume === 0) return;
        
        // Chart area bounds for clipping
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = this.padding.left;
        const maxX = this.logicalWidth - this.padding.right;
        const volumeY = this.padding.top + chartAreaHeight;
        const volumeMaxY = volumeY + this.volumeHeight;
        
        const visibleTimeRange = this.visibleEndTime - this.visibleStartTime;
        const intervalMs = this.getIntervalMs(this.interval);
        const barWidth = visibleTimeRange > 0
            ? (this.chartWidth * intervalMs / visibleTimeRange)
            : (this.chartWidth / visibleCandles.length);
        
        visibleCandles.forEach((candle, index) => {
            if (!candle || !candle.time) return;
            
            let x = this.timeToX(candle.time) - barWidth / 2;
            const height = (visibleVolumes[index] / maxVolume) * this.volumeHeight;
            
            if (isNaN(x) || isNaN(height) || height <= 0) return;
            
            // Clip X position to bounds
            const clippedX = Math.max(minX, Math.min(maxX - barWidth * 0.7, x));
            const clippedWidth = Math.min(barWidth * 0.7, maxX - clippedX);
            
            // Clip height to volume area
            const clippedHeight = Math.min(height, volumeMaxY - volumeY);
            
            if (clippedWidth > 0 && clippedHeight > 0) {
                // Volume bars are grey
                this.ctx.fillStyle = '#666';
                this.ctx.fillRect(clippedX, volumeY + this.volumeHeight - clippedHeight, clippedWidth, clippedHeight);
            }
        });
        this.drawVolumeMAVOL(volumeY, volumeMaxY, minX, maxX, maxVolume);
    }
    
    drawVolumeMAVOL(volumeY, volumeMaxY, minX, maxX, maxVolume) {
        const subVol = this.activeIndicators.subVol;
        if (!subVol || !this.volumeData?.length || maxVolume <= 0) return;
        const drawMavolLine = (values, color, lineWidth) => {
            if (!values || values.length === 0) return;
            let started = false;
            this.ctx.beginPath();
            this.ctx.strokeStyle = color;
            this.ctx.lineWidth = lineWidth || 2;
            this.ctx.setLineDash([]);
            for (let i = 0; i < this.candles.length; i++) {
                const val = values[i];
                if (val == null || isNaN(val) || val <= 0) continue;
                const x = this.timeToX(this.candles[i].time);
                if (x < minX || x > maxX) { started = false; continue; }
                const t = val / maxVolume;
                const y = volumeMaxY - t * this.volumeHeight;
                if (!started) { this.ctx.moveTo(x, y); started = true; } else this.ctx.lineTo(x, y);
            }
            this.ctx.stroke();
        };
        if (subVol.mavol1?.en && subVol.mavol1.period >= 1) {
            const mavol1Values = this.computeMA(this.volumeData, subVol.mavol1.period);
            drawMavolLine(mavol1Values, subVol.mavol1.color || '#03a9f4', subVol.mavol1.lineWidth || 2);
        }
        if (subVol.mavol2?.en && subVol.mavol2.period >= 1) {
            const mavol2Values = this.computeMA(this.volumeData, subVol.mavol2.period);
            drawMavolLine(mavol2Values, subVol.mavol2.color || '#e91e63', subVol.mavol2.lineWidth || 2);
        }
    }
    
    drawYAxis() {
        // Calculate price levels based on visible range
        const visiblePriceRange = this.visibleMaxPrice - this.visibleMinPrice;
        const numLevels = 5;
        const priceStep = visiblePriceRange / (numLevels - 1);
        
        this.ctx.fillStyle = '#fff';
        this.ctx.font = '11px sans-serif';
        this.ctx.textAlign = 'left';
        
        for (let i = 0; i < numLevels; i++) {
            const price = this.visibleMinPrice + i * priceStep;
            const y = this.priceToY(price);
            const label = this.formatPrice(price);
            this.ctx.fillText(label, this.logicalWidth - this.padding.right + 5, y + 4);
        }
    }
    
    drawXAxis() {
        // Calculate time labels based on visible range
        const visibleTimeRange = this.visibleEndTime - this.visibleStartTime;
        const numLabels = 10;
        const timeStep = visibleTimeRange / numLabels;
        
        this.ctx.fillStyle = '#fff';
        this.ctx.font = '11px sans-serif';
        this.ctx.textAlign = 'center';
        
        for (let i = 0; i <= numLabels; i++) {
            const time = this.visibleStartTime + i * timeStep;
            const x = this.timeToX(time);
            const label = this.formatTime(time);
            
            this.ctx.fillText(label, x, this.logicalHeight - this.padding.bottom + 20);
        }
    }
    
    drawWatermark() {
        this.ctx.save();
        this.ctx.globalAlpha = 0.15;
        this.ctx.fillStyle = '#888';
        this.ctx.font = 'bold 140px sans-serif';
        this.ctx.textAlign = 'center';
        this.ctx.textBaseline = 'middle';
        // Position watermark in center of chart area (not including volume)
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const chartCenterY = this.padding.top + chartAreaHeight / 2;
        this.ctx.fillText('PTB', this.logicalWidth / 2, chartCenterY);
        this.ctx.restore();
    }
    
    drawRulerSelections() {
        const hasRulerSelections = this.rulerSelections.length > 0 || this.currentRulerSelection;
        
        if (!hasRulerSelections) {
            return;
        }
        
        this.ctx.save();
        
        // Chart bounds for clipping - exact boundaries matching axes
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        // Use exact pixel boundaries - no rounding errors
        const minX = Math.ceil(this.padding.left);
        const minY = Math.ceil(this.padding.top);
        const maxX = Math.floor(this.logicalWidth - this.padding.right);
        const maxY = Math.floor(this.padding.top + chartAreaHeight);
        
        // Set strict clipping region to chart area (excluding volume and axes)
        this.ctx.beginPath();
        this.ctx.rect(minX, minY, maxX - minX, maxY - minY);
        this.ctx.clip();
        
        this.ctx.setLineDash([]);
        
        // Draw completed selections (привязка к данным: time/price -> x,y)
        this.rulerSelections.forEach((selection, index) => {
            const selected = this.selectedDrawing?.type === 'ruler' && this.selectedDrawing?.index === index;
            let x1, y1, x2, y2;
            if (selection.time1 != null && selection.price1 != null) {
                x1 = this.timeToX(selection.time1);
                y1 = this.priceToY(selection.price1);
                x2 = this.timeToX(selection.time2);
                y2 = this.priceToY(selection.price2);
            } else {
                x1 = selection.x1; y1 = selection.y1; x2 = selection.x2; y2 = selection.y2;
            }
            let x = Math.min(x1, x2);
            let y = Math.min(y1, y2);
            let width = Math.abs(x2 - x1);
            let height = Math.abs(y2 - y1);
            const clippedX = Math.max(minX, x);
            const clippedY = Math.max(minY, y);
            const clippedWidth = Math.min(maxX, x + width) - clippedX;
            const clippedHeight = Math.min(maxY, y + height) - clippedY;
            if (clippedWidth > 0 && clippedHeight > 0) {
                this.ctx.fillStyle = selected ? 'rgba(255, 167, 38, 0.25)' : 'rgba(76, 175, 80, 0.3)';
                this.ctx.fillRect(clippedX, clippedY, clippedWidth, clippedHeight);
                this.ctx.strokeStyle = selected ? '#ffa726' : '#4caf50';
                this.ctx.lineWidth = selected ? 4 : 2;
                this.ctx.strokeRect(clippedX, clippedY, clippedWidth, clippedHeight);
                if (selection.summary && width > 80 && height > 50) {
                    if (x + 150 <= maxX && y + 80 <= maxY) {
                        this.drawRulerSummaryBox(x, y, width, height, selection.summary);
                    }
                }
            }
        });
        
        // Draw current selection being dragged (with dynamic updates)
        if (this.currentRulerSelection) {
            let x = Math.min(this.currentRulerSelection.x1, this.currentRulerSelection.x2);
            let y = Math.min(this.currentRulerSelection.y1, this.currentRulerSelection.y2);
            let width = Math.abs(this.currentRulerSelection.x2 - this.currentRulerSelection.x1);
            let height = Math.abs(this.currentRulerSelection.y2 - this.currentRulerSelection.y1);
            
            // Clip rectangle to chart bounds
            const clippedX = Math.max(minX, x);
            const clippedY = Math.max(minY, y);
            const clippedWidth = Math.min(maxX, x + width) - clippedX;
            const clippedHeight = Math.min(maxY, y + height) - clippedY;
            
            if (clippedWidth > 0 && clippedHeight > 0) {
                // Draw green background with more transparency for preview
                this.ctx.fillStyle = 'rgba(76, 175, 80, 0.2)';
                this.ctx.fillRect(clippedX, clippedY, clippedWidth, clippedHeight);
                
                // Draw border
                this.ctx.strokeStyle = '#4caf50';
                this.ctx.lineWidth = 2;
                this.ctx.strokeRect(clippedX, clippedY, clippedWidth, clippedHeight);
            }
            
            // Calculate and show preview summary dynamically
            if (width > 10 && height > 10) {
                const summary = this.calculateRulerSummary(this.currentRulerSelection);
                
                if (width > 80 && height > 50) {
                    // Only draw if text box would be visible
                    if (x + 150 <= maxX && y + 80 <= maxY) {
                        this.drawRulerSummaryBox(x, y, width, height, summary);
                    }
                }
            }
        }
        
        this.ctx.restore();
    }
    
    drawRulerSummaryBox(x, y, width, height, summary) {
        this.ctx.save();
        
        const padding = 10;
        const lineHeight = 16;
        
        // Format lines like in image: "+16.89%", "3н 9ч", "513 бара"
        const lines = [
            summary.percentChange || '0%',
            summary.timePeriod || '0н 0ч',
            `${summary.bars || summary.count || 0} бара`
        ];
        
        // Calculate text dimensions
        this.ctx.font = 'bold 12px sans-serif';
        const textWidth = Math.max(...lines.map(l => this.ctx.measureText(l).width));
        const textHeight = lines.length * lineHeight;
        const boxWidth = textWidth + padding * 2;
        const boxHeight = textHeight + padding * 2;
        
        // Position box inside selection (top-left corner)
        const boxX = x + padding;
        const boxY = y + padding;
        
        // Make sure box fits
        if (boxX + boxWidth <= this.logicalWidth && boxY + boxHeight <= this.logicalHeight) {
            // Draw green background box
            this.ctx.fillStyle = 'rgba(76, 175, 80, 0.9)'; // Green background
            this.ctx.fillRect(boxX, boxY, boxWidth, boxHeight);
            
            // Draw border
            this.ctx.strokeStyle = '#4caf50';
            this.ctx.lineWidth = 1;
            this.ctx.strokeRect(boxX, boxY, boxWidth, boxHeight);
            
            // Draw text
            this.ctx.fillStyle = '#fff';
            this.ctx.font = 'bold 12px sans-serif';
            this.ctx.textAlign = 'left';
            this.ctx.textBaseline = 'top';
            
            let textY = boxY + padding;
            lines.forEach((line) => {
                this.ctx.fillText(line, boxX + padding, textY);
                textY += lineHeight;
            });
        }
        
        this.ctx.restore();
    }
    
    clipLineToBounds(x1, y1, x2, y2, minX, minY, maxX, maxY) {
        // Cohen-Sutherland line clipping algorithm
        const INSIDE = 0;
        const LEFT = 1;
        const RIGHT = 2;
        const BOTTOM = 4;
        const TOP = 8;
        
        function computeCode(x, y) {
            let code = INSIDE;
            if (x < minX) code |= LEFT;
            else if (x > maxX) code |= RIGHT;
            if (y < minY) code |= BOTTOM;
            else if (y > maxY) code |= TOP;
            return code;
        }
        
        // Handle vertical and horizontal lines
        if (Math.abs(x2 - x1) < 0.001) {
            // Vertical line
            if (x1 < minX || x1 > maxX) return null;
            const clippedY1 = Math.max(minY, Math.min(maxY, y1));
            const clippedY2 = Math.max(minY, Math.min(maxY, y2));
            return { x1: x1, y1: clippedY1, x2: x2, y2: clippedY2 };
        }
        
        if (Math.abs(y2 - y1) < 0.001) {
            // Horizontal line
            if (y1 < minY || y1 > maxY) return null;
            const clippedX1 = Math.max(minX, Math.min(maxX, x1));
            const clippedX2 = Math.max(minX, Math.min(maxX, x2));
            return { x1: clippedX1, y1: y1, x2: clippedX2, y2: y2 };
        }
        
        let code1 = computeCode(x1, y1);
        let code2 = computeCode(x2, y2);
        let accept = false;
        let clippedX1 = x1, clippedY1 = y1, clippedX2 = x2, clippedY2 = y2;
        
        while (true) {
            if ((code1 | code2) === 0) {
                accept = true;
                break;
            } else if ((code1 & code2) !== 0) {
                break;
            } else {
                let x = 0, y = 0;
                const codeOut = code1 !== 0 ? code1 : code2;
                
                if ((codeOut & TOP) !== 0) {
                    x = clippedX1 + (clippedX2 - clippedX1) * (maxY - clippedY1) / (clippedY2 - clippedY1);
                    y = maxY;
                } else if ((codeOut & BOTTOM) !== 0) {
                    x = clippedX1 + (clippedX2 - clippedX1) * (minY - clippedY1) / (clippedY2 - clippedY1);
                    y = minY;
                } else if ((codeOut & RIGHT) !== 0) {
                    y = clippedY1 + (clippedY2 - clippedY1) * (maxX - clippedX1) / (clippedX2 - clippedX1);
                    x = maxX;
                } else if ((codeOut & LEFT) !== 0) {
                    y = clippedY1 + (clippedY2 - clippedY1) * (minX - clippedX1) / (clippedX2 - clippedX1);
                    x = minX;
                }
                
                if (codeOut === code1) {
                    clippedX1 = x;
                    clippedY1 = y;
                    code1 = computeCode(clippedX1, clippedY1);
                } else {
                    clippedX2 = x;
                    clippedY2 = y;
                    code2 = computeCode(clippedX2, clippedY2);
                }
            }
        }
        
        if (accept) {
            // Ensure coordinates are strictly within bounds (no rounding errors)
            clippedX1 = Math.max(minX, Math.min(maxX, clippedX1));
            clippedY1 = Math.max(minY, Math.min(maxY, clippedY1));
            clippedX2 = Math.max(minX, Math.min(maxX, clippedX2));
            clippedY2 = Math.max(minY, Math.min(maxY, clippedY2));
            
            // Final check - ensure line is actually visible
            if (clippedX1 === clippedX2 && clippedY1 === clippedY2) {
                return null; // Line collapsed to a point
            }
            
            return { x1: clippedX1, y1: clippedY1, x2: clippedX2, y2: clippedY2 };
        }
        
        return null;
    }
    
    drawDrawnLines() {
        const hasBrushLines = this.drawnLines.length > 0 || (this.currentLine && this.tempPoint);
        const hasHorizontalLines = this.horizontalLines.length > 0;
        const hasRectangles = this.rectangles.length > 0 || (this.currentRectangle && this.tempPoint);
        
        if (!hasBrushLines && !hasHorizontalLines && !hasRectangles) {
            return;
        }
        
        this.ctx.save();
        
        // Chart bounds for clipping - exact boundaries matching axes
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        // Use exact pixel boundaries - no rounding errors
        const minX = Math.ceil(this.padding.left);
        const minY = Math.ceil(this.padding.top);
        const maxX = Math.floor(this.logicalWidth - this.padding.right);
        const maxY = Math.floor(this.padding.top + chartAreaHeight);
        
        // Set strict clipping region to chart area (excluding volume and axes)
        this.ctx.beginPath();
        this.ctx.rect(minX, minY, maxX - minX, maxY - minY);
        this.ctx.clip();
        
        this.ctx.setLineDash([]);
        
        // Draw horizontal rays (обычные и alert — прерывистый луч)
        if (hasHorizontalLines) {
            this.horizontalLines.forEach((line, index) => {
                const selected = this.selectedDrawing?.type === 'ray' && this.selectedDrawing?.index === index;
                const isAlert = !!line.alert;
                this.ctx.strokeStyle = selected ? '#ffa726' : (isAlert ? '#ff9800' : '#4a9eff');
                this.ctx.lineWidth = selected ? 4 : 2;
                if (isAlert) this.ctx.setLineDash([8, 4]);
                let x1, y1, x2, y2;
                if (line.time1 != null && line.price != null) {
                    x1 = this.timeToX(line.time1);
                    y1 = this.priceToY(line.price);
                    x2 = maxX;
                    y2 = y1;
                } else {
                    x1 = line.x1; y1 = line.y1; x2 = line.x2; y2 = line.y2;
                }
                const clipped = this.clipLineToBounds(x1, y1, x2, y2, minX, minY, maxX, maxY);
                if (clipped) {
                    this.ctx.beginPath();
                    this.ctx.moveTo(clipped.x1, clipped.y1);
                    this.ctx.lineTo(clipped.x2, clipped.y2);
                    this.ctx.stroke();
                    if (isAlert) this.ctx.setLineDash([]);
                    if (x1 >= minX && x1 <= maxX && y1 >= minY && y1 <= maxY) {
                        this.ctx.fillStyle = selected ? '#ffa726' : (isAlert ? '#ff9800' : '#4a9eff');
                        this.ctx.beginPath();
                        this.ctx.arc(x1, y1, selected ? 5 : 4, 0, Math.PI * 2);
                        this.ctx.fill();
                    }
                }
            });
        }
        
        // Draw rectangles
        if (hasRectangles) {
            this.ctx.strokeStyle = '#4a9eff';
            this.ctx.lineWidth = 2;
            this.ctx.fillStyle = 'rgba(74, 158, 255, 0.1)'; // Semi-transparent fill
            
            // Draw completed rectangles
            this.rectangles.forEach((rect, index) => {
                const selected = this.selectedDrawing?.type === 'rect' && this.selectedDrawing?.index === index;
                this.ctx.strokeStyle = selected ? '#ffa726' : '#4a9eff';
                this.ctx.lineWidth = selected ? 4 : 2;
                let x1, y1, x2, y2;
                if (rect.time1 != null && rect.price1 != null) {
                    x1 = this.timeToX(rect.time1);
                    y1 = this.priceToY(rect.price1);
                    x2 = this.timeToX(rect.time2);
                    y2 = this.priceToY(rect.price2);
                } else {
                    x1 = rect.x1; y1 = rect.y1; x2 = rect.x2; y2 = rect.y2;
                }
                let x = Math.min(x1, x2);
                let y = Math.min(y1, y2);
                let width = Math.abs(x2 - x1);
                let height = Math.abs(y2 - y1);
                const clippedX = Math.max(minX, x);
                const clippedY = Math.max(minY, y);
                const clippedWidth = Math.min(maxX, x + width) - clippedX;
                const clippedHeight = Math.min(maxY, y + height) - clippedY;
                if (clippedWidth > 0 && clippedHeight > 0) {
                    this.ctx.fillRect(clippedX, clippedY, clippedWidth, clippedHeight);
                    this.ctx.strokeRect(clippedX, clippedY, clippedWidth, clippedHeight);
                }
                this.ctx.fillStyle = selected ? '#ffa726' : '#4a9eff';
                if (x1 >= minX && x1 <= maxX && y1 >= minY && y1 <= maxY) {
                    this.ctx.beginPath();
                    this.ctx.arc(x1, y1, selected ? 5 : 4, 0, Math.PI * 2);
                    this.ctx.fill();
                }
                if (x2 >= minX && x2 <= maxX && y2 >= minY && y2 <= maxY) {
                    this.ctx.beginPath();
                    this.ctx.arc(x2, y2, selected ? 5 : 4, 0, Math.PI * 2);
                    this.ctx.fill();
                }
            });
            
            // Draw current rectangle being created (with preview)
            if (this.currentRectangle && this.tempPoint) {
                this.ctx.fillStyle = 'rgba(74, 158, 255, 0.1)';
                this.ctx.strokeStyle = '#4a9eff';
                this.ctx.lineWidth = 2;
                let x = Math.min(this.currentRectangle.x1, this.tempPoint.x);
                let y = Math.min(this.currentRectangle.y1, this.tempPoint.y);
                let width = Math.abs(this.tempPoint.x - this.currentRectangle.x1);
                let height = Math.abs(this.tempPoint.y - this.currentRectangle.y1);
                
                // Clip rectangle to chart bounds
                const clippedX = Math.max(minX, x);
                const clippedY = Math.max(minY, y);
                const clippedWidth = Math.min(maxX, x + width) - clippedX;
                const clippedHeight = Math.min(maxY, y + height) - clippedY;
                
                if (clippedWidth > 0 && clippedHeight > 0) {
                    // Preview rectangle with transparency
                    this.ctx.globalAlpha = 0.5;
                    this.ctx.fillRect(clippedX, clippedY, clippedWidth, clippedHeight);
                    this.ctx.globalAlpha = 0.7;
                    this.ctx.strokeRect(clippedX, clippedY, clippedWidth, clippedHeight);
                }
                
                // Draw first point (more visible, only if visible)
                this.ctx.globalAlpha = 1;
                if (this.currentRectangle.x1 >= minX && this.currentRectangle.x1 <= maxX && 
                    this.currentRectangle.y1 >= minY && this.currentRectangle.y1 <= maxY) {
                    this.ctx.fillStyle = '#4a9eff';
                    this.ctx.beginPath();
                    this.ctx.arc(this.currentRectangle.x1, this.currentRectangle.y1, 4, 0, Math.PI * 2);
                    this.ctx.fill();
                }
                
                // Draw preview corner point (only if visible)
                if (this.tempPoint.x >= minX && this.tempPoint.x <= maxX && 
                    this.tempPoint.y >= minY && this.tempPoint.y <= maxY) {
                    this.ctx.beginPath();
                    this.ctx.arc(this.tempPoint.x, this.tempPoint.y, 4, 0, Math.PI * 2);
                    this.ctx.fill();
                }
            }
        }
        
        // Draw brush lines
        if (hasBrushLines) {
            this.ctx.strokeStyle = '#4a9eff';
            this.ctx.lineWidth = 2;
            
            // Draw completed lines
            this.drawnLines.forEach((line, index) => {
                const selected = this.selectedDrawing?.type === 'line' && this.selectedDrawing?.index === index;
                this.ctx.strokeStyle = selected ? '#ffa726' : '#4a9eff';
                this.ctx.lineWidth = selected ? 4 : 2;
                let x1, y1, x2, y2;
                if (line.time1 != null && line.price1 != null) {
                    x1 = this.timeToX(line.time1);
                    y1 = this.priceToY(line.price1);
                    x2 = this.timeToX(line.time2);
                    y2 = this.priceToY(line.price2);
                } else {
                    x1 = line.x1; y1 = line.y1; x2 = line.x2; y2 = line.y2;
                }
                const clipped = this.clipLineToBounds(x1, y1, x2, y2, minX, minY, maxX, maxY);
                if (clipped) {
                    this.ctx.beginPath();
                    this.ctx.moveTo(clipped.x1, clipped.y1);
                    this.ctx.lineTo(clipped.x2, clipped.y2);
                    this.ctx.stroke();
                    this.ctx.fillStyle = selected ? '#ffa726' : '#4a9eff';
                    if (x1 >= minX && x1 <= maxX && y1 >= minY && y1 <= maxY) {
                        this.ctx.beginPath();
                        this.ctx.arc(x1, y1, selected ? 5 : 3, 0, Math.PI * 2);
                        this.ctx.fill();
                    }
                    if (x2 >= minX && x2 <= maxX && y2 >= minY && y2 <= maxY) {
                        this.ctx.beginPath();
                        this.ctx.arc(x2, y2, selected ? 5 : 3, 0, Math.PI * 2);
                        this.ctx.fill();
                    }
                }
            });
            
            // Draw current line being created (with preview)
            if (this.currentLine && this.tempPoint) {
                // Clip line to chart bounds
                const clipped = this.clipLineToBounds(this.currentLine.x1, this.currentLine.y1, this.tempPoint.x, this.tempPoint.y, minX, minY, maxX, maxY);
                if (clipped) {
                    this.ctx.strokeStyle = '#4a9eff';
                    this.ctx.globalAlpha = 0.7;
                    this.ctx.beginPath();
                    this.ctx.moveTo(clipped.x1, clipped.y1);
                    this.ctx.lineTo(clipped.x2, clipped.y2);
                    this.ctx.stroke();
                }
                
                // Draw first point (more visible, only if visible)
                this.ctx.globalAlpha = 1;
                if (this.currentLine.x1 >= minX && this.currentLine.x1 <= maxX && this.currentLine.y1 >= minY && this.currentLine.y1 <= maxY) {
                    this.ctx.fillStyle = '#4a9eff';
                    this.ctx.beginPath();
                    this.ctx.arc(this.currentLine.x1, this.currentLine.y1, 4, 0, Math.PI * 2);
                    this.ctx.fill();
                }
                
                // Draw preview point (only if visible)
                if (this.tempPoint.x >= minX && this.tempPoint.x <= maxX && this.tempPoint.y >= minY && this.tempPoint.y <= maxY) {
                    this.ctx.beginPath();
                    this.ctx.arc(this.tempPoint.x, this.tempPoint.y, 3, 0, Math.PI * 2);
                    this.ctx.fill();
                }
            }
        }
        
        this.ctx.restore();
    }
    
    // --- Indicators (MA, EMA, etc.) ---
    getPriceSeries(candles, source) {
        return candles.map(c => c[source] ?? c.close);
    }
    
    computeMA(prices, period) {
        if (!prices.length || period < 1) return [];
        const result = [];
        for (let i = 0; i < prices.length; i++) {
            if (i < period - 1) {
                result.push(null);
            } else {
                let sum = 0;
                for (let j = 0; j < period; j++) sum += prices[i - j];
                result.push(sum / period);
            }
        }
        return result;
    }
    
    computeEMA(prices, period) {
        if (!prices.length || period < 1) return [];
        const k = 2 / (period + 1);
        const result = [];
        for (let i = 0; i < prices.length; i++) {
            if (i < period - 1) {
                result.push(null);
            } else if (i === period - 1) {
                let sum = 0;
                for (let j = 0; j < period; j++) sum += prices[j];
                result.push(sum / period);
            } else {
                result.push(prices[i] * k + result[i - 1] * (1 - k));
            }
        }
        return result;
    }
    
    computeWMA(prices, period) {
        if (!prices.length || period < 1) return [];
        const result = [];
        const weightSum = (period * (period + 1)) / 2;
        for (let i = 0; i < prices.length; i++) {
            if (i < period - 1) {
                result.push(null);
            } else {
                let sum = 0;
                for (let j = 0; j < period; j++) sum += (j + 1) * prices[i - j];
                result.push(sum / weightSum);
            }
        }
        return result;
    }
    
    computeBOLL(candles, period, stdMult) {
        if (!candles?.length || period < 2) return { upper: [], middle: [], lower: [] };
        const close = candles.map(c => c.close);
        const middle = this.computeMA(close, period);
        const upper = [];
        const lower = [];
        for (let i = 0; i < close.length; i++) {
            if (i < period - 1 || middle[i] == null) {
                upper.push(null);
                lower.push(null);
            } else {
                let sumSq = 0;
                for (let j = 0; j < period; j++) sumSq += Math.pow(close[i - j] - middle[i], 2);
                const std = Math.sqrt(sumSq / period);
                upper.push(middle[i] + stdMult * std);
                lower.push(middle[i] - stdMult * std);
            }
        }
        return { upper, middle, lower };
    }
    
    computeVWAP(candles, volumeData) {
        if (!candles?.length) return [];
        const result = [];
        let cumTPV = 0;
        let cumVol = 0;
        for (let i = 0; i < candles.length; i++) {
            const c = candles[i];
            const vol = (volumeData && volumeData[i] != null) ? volumeData[i] : 0;
            const tp = (c.high + c.low + c.close) / 3;
            cumTPV += tp * vol;
            cumVol += vol;
            result.push(cumVol > 0 ? cumTPV / cumVol : tp);
        }
        return result;
    }
    
    computeSAR(candles, step, maxStep) {
        if (!candles?.length || step <= 0) return [];
        const result = [];
        let sar = candles[0].low;
        let ep = candles[0].high;
        let af = step;
        let trend = 1; // 1 = up, -1 = down
        result.push(sar);
        for (let i = 1; i < candles.length; i++) {
            const high = candles[i].high;
            const low = candles[i].low;
            if (trend === 1) {
                if (low < sar) {
                    trend = -1;
                    sar = ep;
                    ep = low;
                    af = step;
                } else {
                    if (high > ep) {
                        ep = high;
                        af = Math.min(af + step, maxStep);
                    }
                    sar = sar + af * (ep - sar);
                    if (sar > low) sar = low;
                    if (sar > candles[i - 1].low) sar = candles[i - 1].low;
                }
            } else {
                if (high > sar) {
                    trend = 1;
                    sar = ep;
                    ep = high;
                    af = step;
                } else {
                    if (low < ep) {
                        ep = low;
                        af = Math.min(af + step, maxStep);
                    }
                    sar = sar + af * (ep - sar);
                    if (sar < high) sar = high;
                    if (sar < candles[i - 1].high) sar = candles[i - 1].high;
                }
            }
            result.push(sar);
        }
        return result;
    }
    
    computeMACD(candles, fastPeriod, slowPeriod, signalPeriod) {
        if (!candles?.length || fastPeriod < 1 || slowPeriod < fastPeriod) return { macd: [], signal: [], hist: [] };
        const close = candles.map(c => c.close);
        const emaFast = this.computeEMA(close, fastPeriod);
        const emaSlow = this.computeEMA(close, slowPeriod);
        const macd = [];
        for (let i = 0; i < close.length; i++) {
            if (emaFast[i] != null && emaSlow[i] != null) macd.push(emaFast[i] - emaSlow[i]);
            else macd.push(null);
        }
        const macdForEma = macd.map(x => x ?? 0);
        const signal = this.computeEMA(macdForEma, signalPeriod);
        const hist = [];
        for (let i = 0; i < macd.length; i++) {
            if (macd[i] != null && signal[i] != null) hist.push(macd[i] - signal[i]);
            else hist.push(null);
        }
        return { macd, signal, hist };
    }
    
    computeRSI(prices, period) {
        if (!prices.length || period < 2) return [];
        const result = [];
        let avgGain = 0, avgLoss = 0;
        for (let i = 0; i < prices.length; i++) {
            if (i < 1) {
                result.push(null);
                continue;
            }
            const gain = prices[i] > prices[i - 1] ? prices[i] - prices[i - 1] : 0;
            const loss = prices[i] < prices[i - 1] ? prices[i - 1] - prices[i] : 0;
            if (i < period) {
                result.push(null);
                continue;
            }
            if (i === period) {
                let sumG = 0, sumL = 0;
                for (let j = 1; j <= period; j++) {
                    const d = prices[i - j + 1] - prices[i - j];
                    if (d > 0) sumG += d; else sumL -= d;
                }
                avgGain = sumG / period;
                avgLoss = sumL / period;
            } else {
                avgGain = (avgGain * (period - 1) + gain) / period;
                avgLoss = (avgLoss * (period - 1) + loss) / period;
            }
            result.push(avgLoss === 0 ? 100 : (100 - (100 / (1 + avgGain / avgLoss))));
        }
        return result;
    }
    
    computeOBV(candles, volumeData) {
        if (!candles?.length) return [];
        const result = [];
        let obv = 0;
        for (let i = 0; i < candles.length; i++) {
            const vol = (volumeData && volumeData[i] != null) ? volumeData[i] : 0;
            if (i === 0) obv = vol;
            else {
                if (candles[i].close > candles[i - 1].close) obv += vol;
                else if (candles[i].close < candles[i - 1].close) obv -= vol;
            }
            result.push(obv);
        }
        return result;
    }
    
    computeCCI(candles, period) {
        if (!candles?.length || period < 2) return [];
        const tp = candles.map(c => (c.high + c.low + c.close) / 3);
        const result = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < period - 1) { result.push(null); continue; }
            const slice = tp.slice(i - period + 1, i + 1);
            const sma = slice.reduce((a, b) => a + b, 0) / period;
            const meanDev = slice.reduce((a, b) => a + Math.abs(b - sma), 0) / period;
            const cci = meanDev === 0 ? 0 : (tp[i] - sma) / (0.015 * meanDev);
            result.push(cci);
        }
        return result;
    }
    
    computeWR(candles, period) {
        if (!candles?.length || period < 2) return [];
        const result = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < period - 1) { result.push(null); continue; }
            const high = Math.max(...candles.slice(i - period + 1, i + 1).map(c => c.high));
            const low = Math.min(...candles.slice(i - period + 1, i + 1).map(c => c.low));
            const range = high - low;
            const wr = range === 0 ? -50 : ((high - candles[i].close) / range) * -100;
            result.push(wr);
        }
        return result;
    }
    
    computeMFI(candles, volumeData, period) {
        if (!candles?.length || period < 2) return [];
        const tp = candles.map(c => (c.high + c.low + c.close) / 3);
        const result = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < period) { result.push(null); continue; }
            let pos = 0, neg = 0;
            for (let j = i - period + 1; j <= i; j++) {
                const raw = tp[j] * (volumeData && volumeData[j] != null ? volumeData[j] : 0);
                if (tp[j] > (j > 0 ? tp[j - 1] : tp[j])) pos += raw;
                else if (tp[j] < (j > 0 ? tp[j - 1] : tp[j])) neg += raw;
            }
            const ratio = neg === 0 ? 100 : pos / neg;
            result.push(100 - (100 / (1 + ratio)));
        }
        return result;
    }
    
    computeKDJ(candles, kPeriod, dPeriod) {
        if (!candles?.length || kPeriod < 2) return { k: [], d: [], j: [] };
        const kArr = [], dArr = [], jArr = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < kPeriod - 1) { kArr.push(null); dArr.push(null); jArr.push(null); continue; }
            const slice = candles.slice(i - kPeriod + 1, i + 1);
            const high = Math.max(...slice.map(c => c.high));
            const low = Math.min(...slice.map(c => c.low));
            const rsv = (high === low) ? 50 : ((candles[i].close - low) / (high - low)) * 100;
            const k = i === kPeriod - 1 ? rsv : (kArr[i - 1] != null ? (kArr[i - 1] * 2 / 3 + rsv / 3) : rsv);
            const d = (dArr[i - 1] != null ? (dArr[i - 1] * (dPeriod - 1) / dPeriod + k / dPeriod) : k);
            const j = 3 * k - 2 * d;
            kArr.push(k);
            dArr.push(d);
            jArr.push(j);
        }
        return { k: kArr, d: dArr, j: jArr };
    }
    
    computeStochRSI(rsiValues, stochPeriod) {
        if (!rsiValues?.length || stochPeriod < 2) return [];
        const result = [];
        for (let i = 0; i < rsiValues.length; i++) {
            if (rsiValues[i] == null || i < stochPeriod - 1) { result.push(null); continue; }
            const slice = rsiValues.slice(i - stochPeriod + 1, i + 1).filter(v => v != null);
            if (slice.length < stochPeriod) { result.push(null); continue; }
            const r = Math.max(...slice) - Math.min(...slice);
            const stoch = r === 0 ? 50 : ((rsiValues[i] - Math.min(...slice)) / r) * 100;
            result.push(stoch);
        }
        return result;
    }
    
    computeStochRSIKD(rsiValues, stochPeriod, smoothK, smoothD) {
        const rawK = this.computeStochRSI(rsiValues, stochPeriod);
        if (!rawK.length) return { k: [], d: [] };
        const smooth = (arr, period) => {
            const out = [];
            for (let i = 0; i < arr.length; i++) {
                if (i < period - 1) { out.push(null); continue; }
                const slice = arr.slice(i - period + 1, i + 1);
                if (slice.some(v => v == null || isNaN(v))) { out.push(null); continue; }
                out.push(slice.reduce((a, b) => a + b, 0) / period);
            }
            return out;
        };
        const k = smooth(rawK, smoothK);
        const d = smooth(k, smoothD);
        return { k, d };
    }
    
    computeDMI(candles, period) {
        if (!candles?.length || period < 2) return { plus: [], minus: [] };
        const dmPlus = [], dmMinus = [], tr = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < 1) {
                dmPlus.push(0);
                dmMinus.push(candles[i].high - candles[i].low);
                tr.push(candles[i].high - candles[i].low);
                continue;
            }
            const up = candles[i].high - candles[i - 1].high;
            const down = candles[i - 1].low - candles[i].low;
            dmPlus.push(up > down && up > 0 ? up : 0);
            dmMinus.push(down > up && down > 0 ? down : 0);
            tr.push(Math.max(
                candles[i].high - candles[i].low,
                Math.abs(candles[i].high - candles[i - 1].close),
                Math.abs(candles[i].low - candles[i - 1].close)
            ));
        }
        const wilder = (arr, per) => {
            const out = [];
            for (let i = 0; i < arr.length; i++) {
                if (i < per - 1) { out.push(null); continue; }
                if (i === per - 1) {
                    let sum = 0;
                    for (let j = 0; j < per; j++) sum += arr[i - j];
                    out.push(sum);
                } else {
                    out.push(out[i - 1] - (out[i - 1] / per) + arr[i]);
                }
            }
            return out;
        };
        const smoothPlus = wilder(dmPlus, period);
        const smoothMinus = wilder(dmMinus, period);
        const smoothTR = wilder(tr, period);
        const plus = [], minus = [];
        for (let i = 0; i < candles.length; i++) {
            if (smoothTR[i] == null || smoothTR[i] === 0) { plus.push(null); minus.push(null); continue; }
            plus.push((smoothPlus[i] / smoothTR[i]) * 100);
            minus.push((smoothMinus[i] / smoothTR[i]) * 100);
        }
        return { plus, minus };
    }
    
    computeDMIWithADX(candles, period) {
        const { plus, minus } = this.computeDMI(candles, period);
        if (!plus.length) return { plus, minus, adx: [] };
        const dx = [];
        for (let i = 0; i < plus.length; i++) {
            if (plus[i] == null || minus[i] == null) { dx.push(null); continue; }
            const sum = plus[i] + minus[i];
            dx.push(sum === 0 ? 0 : (100 * Math.abs(plus[i] - minus[i])) / sum);
        }
        const adx = [];
        let smoothDx = 0;
        for (let i = 0; i < dx.length; i++) {
            if (dx[i] == null) { adx.push(null); continue; }
            if (i < period - 1) { adx.push(null); continue; }
            if (i === period - 1) {
                let sum = 0, count = 0;
                for (let j = 0; j < period; j++) if (dx[i - j] != null) { sum += dx[i - j]; count++; }
                smoothDx = count >= period ? sum / period : dx[i];
                adx.push(smoothDx);
            } else {
                smoothDx = smoothDx - (smoothDx / period) + dx[i];
                adx.push(smoothDx);
            }
        }
        return { plus, minus, adx };
    }
    
    computeMTM(candles, period, source) {
        if (!candles?.length || period < 1) return [];
        const prices = this.getPriceSeries(candles, source || 'close');
        const result = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < period) { result.push(null); continue; }
            result.push(prices[i] - prices[i - period]);
        }
        return result;
    }
    
    computeEMV(candles, period, divisor) {
        if (!candles?.length || period < 2) return [];
        const vol = this.volumeData || [];
        const div = (divisor != null && divisor > 0) ? divisor : 10000;
        const result = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < 1) { result.push(null); continue; }
            const dm = ((candles[i].high + candles[i].low) / 2) - ((candles[i - 1].high + candles[i - 1].low) / 2);
            const br = (vol[i] != null && vol[i] > 0) ? (candles[i].high - candles[i].low) * div / vol[i] : 0;
            const emv = br !== 0 ? dm / br : 0;
            result.push(emv);
        }
        const smoothed = [];
        for (let i = 0; i < result.length; i++) {
            if (i < period - 1) smoothed.push(null);
            else {
                const slice = result.slice(i - period + 1, i + 1).filter(v => v != null && !isNaN(v));
                smoothed.push(slice.length ? slice.reduce((a, b) => a + b, 0) / slice.length : null);
            }
        }
        return smoothed;
    }
    
    computeTRIX(candles, period) {
        if (!candles?.length || period < 1) return [];
        const close = candles.map(c => c.close);
        const ema1 = this.computeEMA(close, period);
        const ema2 = this.computeEMA(ema1.map(x => x ?? 0), period);
        const ema3 = this.computeEMA(ema2, period);
        return ema3;
    }
    
    computeSuperTrend(candles, period, multiplier) {
        if (!candles?.length || period < 1 || multiplier <= 0) return [];
        const tr = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < 1) tr.push(candles[i].high - candles[i].low);
            else tr.push(Math.max(
                candles[i].high - candles[i].low,
                Math.abs(candles[i].high - candles[i - 1].close),
                Math.abs(candles[i].low - candles[i - 1].close)
            ));
        }
        const atr = [];
        for (let i = 0; i < candles.length; i++) {
            if (i < period - 1) { atr.push(null); continue; }
            if (i === period - 1) {
                let sum = 0;
                for (let j = 0; j < period; j++) sum += tr[j];
                atr.push(sum / period);
            } else {
                atr.push((atr[i - 1] * (period - 1) + tr[i]) / period);
            }
        }
        const hl2 = candles.map(c => (c.high + c.low) / 2);
        const result = [];
        let upperBand = 0, lowerBand = 0, trend = 1;
        for (let i = 0; i < candles.length; i++) {
            if (i < period) { result.push(null); continue; }
            const atrVal = atr[i];
            const upBand = hl2[i] - multiplier * atrVal;
            const dnBand = hl2[i] + multiplier * atrVal;
            if (i === period) {
                upperBand = dnBand;
                lowerBand = upBand;
                result.push(upBand);
                trend = 1;
                continue;
            }
            if (upBand > lowerBand) lowerBand = upBand;
            if (dnBand < upperBand) upperBand = dnBand;
            if (trend === 1) {
                if (candles[i].close < lowerBand) { trend = -1; result.push(upperBand); upperBand = dnBand; lowerBand = upBand; }
                else { result.push(lowerBand); if (upBand > lowerBand) lowerBand = upBand; }
            } else {
                if (candles[i].close > upperBand) { trend = 1; result.push(lowerBand); lowerBand = upBand; upperBand = dnBand; }
                else { result.push(upperBand); if (dnBand < upperBand) upperBand = dnBand; }
            }
        }
        return result;
    }
    
    drawIndicators() {
        if (!this.candles || this.candles.length === 0) return;
        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = this.padding.left;
        const minY = this.padding.top;
        const maxX = this.logicalWidth - this.padding.right;
        const maxY = this.padding.top + chartAreaHeight;
        
        const drawIndicatorLine = (values) => {
            if (!values || values.length === 0) return;
            let started = false;
            this.ctx.beginPath();
            for (let i = 0; i < this.candles.length; i++) {
                const val = values[i];
                if (val == null || isNaN(val)) continue;
                const x = this.timeToX(this.candles[i].time);
                const y = this.priceToY(val);
                if (x < minX || x > maxX || y < minY || y > maxY) {
                    started = false;
                    continue;
                }
                if (!started) {
                    this.ctx.moveTo(x, y);
                    started = true;
                } else {
                    this.ctx.lineTo(x, y);
                }
            }
            this.ctx.stroke();
        };
        const drawIndicatorLineScaled = (values, valMin, valMax, pixelYTop, pixelYBottom) => {
            if (!values || values.length === 0 || valMax === valMin) return;
            let started = false;
            this.ctx.beginPath();
            const range = valMax - valMin;
            for (let i = 0; i < this.candles.length; i++) {
                const val = values[i];
                if (val == null || isNaN(val)) continue;
                const x = this.timeToX(this.candles[i].time);
                if (x < minX || x > maxX) { started = false; continue; }
                const t = (val - valMin) / range;
                const y = pixelYBottom - t * (pixelYBottom - pixelYTop);
                if (!started) {
                    this.ctx.moveTo(x, y);
                    started = true;
                } else {
                    this.ctx.lineTo(x, y);
                }
            }
            this.ctx.stroke();
        };
        
        ['ma', 'ema', 'wma'].forEach(type => {
            const list = this.activeIndicators[type];
            if (!list || !list.length) return;
            list.forEach(({ period, source, color, lineWidth }) => {
                if (!period || period < 1) return;
                const prices = this.getPriceSeries(this.candles, source);
                let values;
                if (type === 'ma') values = this.computeMA(prices, period);
                else if (type === 'ema') values = this.computeEMA(prices, period);
                else if (type === 'wma') values = this.computeWMA(prices, period);
                else return;
                this.ctx.strokeStyle = color || '#ffeb3b';
                this.ctx.lineWidth = (lineWidth != null && lineWidth >= 1 && lineWidth <= 4) ? lineWidth : 2;
                this.ctx.setLineDash([]);
                drawIndicatorLine(values);
            });
        });
        
        if (this.activeIndicators.boll) {
            const { period, std, colorUpper, colorMid, colorLower } = this.activeIndicators.boll;
            const { upper, middle, lower } = this.computeBOLL(this.candles, period, std);
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            this.ctx.strokeStyle = colorUpper || '#2196f3';
            drawIndicatorLine(upper);
            this.ctx.strokeStyle = colorMid || '#ff9800';
            drawIndicatorLine(middle);
            this.ctx.strokeStyle = colorLower || '#2196f3';
            drawIndicatorLine(lower);
        }
        
        if (this.activeIndicators.vwap) {
            const values = this.computeVWAP(this.candles, this.volumeData);
            this.ctx.strokeStyle = this.activeIndicators.vwap.color || '#00bcd4';
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            drawIndicatorLine(values);
        }
        
        if (this.activeIndicators.sar) {
            const { step, max: maxStep, color } = this.activeIndicators.sar;
            const values = this.computeSAR(this.candles, step, maxStep);
            this.ctx.strokeStyle = color || '#f44336';
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            drawIndicatorLine(values);
        }
        if (this.activeIndicators.macd) {
            const { fast, slow, signal: sigPeriod, colorMacd, colorSignal } = this.activeIndicators.macd;
            const { macd, signal } = this.computeMACD(this.candles, fast, slow, sigPeriod);
            const allVals = [...macd, ...signal].filter(v => v != null && !isNaN(v));
            const vMin = allVals.length ? Math.min(...allVals) : 0;
            const vMax = allVals.length ? Math.max(...allVals) : 0;
            const bandHeight = chartAreaHeight * 0.12;
            const bandTop = maxY - bandHeight;
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            this.ctx.strokeStyle = colorMacd || '#2196f3';
            drawIndicatorLineScaled(macd, vMin, vMax, bandTop, maxY);
            this.ctx.strokeStyle = colorSignal || '#ff9800';
            drawIndicatorLineScaled(signal, vMin, vMax, bandTop, maxY);
        }
        if (this.activeIndicators.rsi) {
            const { period, color } = this.activeIndicators.rsi;
            const close = this.candles.map(c => c.close);
            const values = this.computeRSI(close, period);
            const bandHeight = chartAreaHeight * 0.12;
            const rsiBottom = this.activeIndicators.macd ? maxY - bandHeight : maxY;
            const rsiTop = rsiBottom - bandHeight;
            this.ctx.strokeStyle = color || '#9c27b0';
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            drawIndicatorLineScaled(values, 0, 100, rsiTop, rsiBottom);
        }
        if (this.activeIndicators.trix) {
            const { period, color } = this.activeIndicators.trix;
            const values = this.computeTRIX(this.candles, period);
            this.ctx.strokeStyle = color || '#00bcd4';
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            drawIndicatorLine(values);
        }
        if (this.activeIndicators.super) {
            const { period, multiplier, color } = this.activeIndicators.super;
            const values = this.computeSuperTrend(this.candles, period, multiplier);
            this.ctx.strokeStyle = color || '#f44336';
            this.ctx.lineWidth = 2;
            this.ctx.setLineDash([]);
            drawIndicatorLine(values);
        }
        if (this.activeIndicators.subMacd) {
            const cfg = this.activeIndicators.subMacd;
            const { fast, slow, signal: sigPeriod, dif, dea, hist } = cfg;
            const { macd: difValues, signal: deaValues, hist: histValues } = this.computeMACD(this.candles, fast, slow, sigPeriod);
            const allVals = [...difValues, ...deaValues, ...histValues].filter(v => v != null && !isNaN(v));
            const vMin = allVals.length ? Math.min(...allVals) : 0;
            const vMax = allVals.length ? Math.max(...allVals) : 0;
            const bandHeight = chartAreaHeight * 0.18;
            const bandTop = maxY - bandHeight;
            const range = vMax - vMin || 1;
            const zeroY = vMin <= 0 && vMax >= 0 ? maxY - (0 - vMin) / range * (maxY - bandTop) : bandTop + bandHeight / 2;
            if (hist?.en && histValues) {
                const barW = Math.max(1, (maxX - minX) / this.candles.length * 0.6);
                const longGrowStyle = cfg.longGrowStyle || 'hollow';
                const longGrowColor = cfg.longGrowColor || '#26a69a';
                const longFallStyle = cfg.longFallStyle || 'filled';
                const longFallColor = cfg.longFallColor || '#26a69a';
                const shortGrowStyle = cfg.shortGrowStyle || 'hollow';
                const shortGrowColor = cfg.shortGrowColor || '#ef5350';
                const shortFallStyle = cfg.shortFallStyle || 'filled';
                const shortFallColor = cfg.shortFallColor || '#ef5350';
                for (let i = 0; i < this.candles.length; i++) {
                    const h = histValues[i];
                    if (h == null || isNaN(h)) continue;
                    const prev = i > 0 ? histValues[i - 1] : null;
                    const isGrow = prev != null && !isNaN(prev) && h > prev;
                    let style, color;
                    if (h >= 0) {
                        style = isGrow ? longGrowStyle : longFallStyle;
                        color = isGrow ? longGrowColor : longFallColor;
                    } else {
                        style = isGrow ? shortGrowStyle : shortFallStyle;
                        color = isGrow ? shortGrowColor : shortFallColor;
                    }
                    const x = this.timeToX(this.candles[i].time);
                    if (x < minX || x > maxX) continue;
                    const t = (h - vMin) / range;
                    const y = maxY - t * (maxY - bandTop);
                    const isFilled = style === 'filled';
                    if (h >= 0) {
                        const top = y, height = zeroY - y;
                        if (isFilled) {
                            this.ctx.fillStyle = color;
                            this.ctx.fillRect(x - barW / 2, top, barW, height);
                        } else {
                            this.ctx.strokeStyle = color;
                            this.ctx.lineWidth = 1;
                            this.ctx.strokeRect(x - barW / 2, top, barW, height);
                        }
                    } else {
                        const top = zeroY, height = y - zeroY;
                        if (isFilled) {
                            this.ctx.fillStyle = color;
                            this.ctx.fillRect(x - barW / 2, top, barW, height);
                        } else {
                            this.ctx.strokeStyle = color;
                            this.ctx.lineWidth = 1;
                            this.ctx.strokeRect(x - barW / 2, top, barW, height);
                        }
                    }
                }
            }
            this.ctx.setLineDash([]);
            if (dif?.en) {
                this.ctx.strokeStyle = dif.color || '#9c27b0';
                this.ctx.lineWidth = (dif.lineWidth != null && dif.lineWidth >= 1 && dif.lineWidth <= 4) ? dif.lineWidth : 2;
                drawIndicatorLineScaled(difValues, vMin, vMax, bandTop, maxY);
            }
            if (dea?.en) {
                this.ctx.strokeStyle = dea.color || '#e91e63';
                this.ctx.lineWidth = (dea.lineWidth != null && dea.lineWidth >= 1 && dea.lineWidth <= 4) ? dea.lineWidth : 2;
                drawIndicatorLineScaled(deaValues, vMin, vMax, bandTop, maxY);
            }
        }
        const subMacdBandH = chartAreaHeight * 0.18;
        let subBandBottom = maxY - subMacdBandH;
        const subBandH = chartAreaHeight * 0.12;
        const subIndicators = [
            { key: 'subRsi', draw: () => { const c = this.activeIndicators.subRsi; if (!c || !c.lines?.length) return; const close = this.candles.map(x => x.close); c.lines.forEach(line => { if (!line || !line.en || line.period < 2) return; const vals = this.computeRSI(close, line.period); this.ctx.strokeStyle = line.color || '#9c27b0'; this.ctx.lineWidth = (line.lineWidth != null && line.lineWidth >= 1 && line.lineWidth <= 4) ? line.lineWidth : 2; this.ctx.setLineDash([]); drawIndicatorLineScaled(vals, 0, 100, subBandBottom - subBandH, subBandBottom); }); } },
            { key: 'subObv', draw: () => { const c = this.activeIndicators.subObv; if (!c) return; const obvVals = this.computeOBV(this.candles, this.volumeData); const all = obvVals.filter(v => v != null && !isNaN(v)); let vMin = all.length ? Math.min(...all) : 0, vMax = all.length ? Math.max(...all) : 1; let maVals = null, emaVals = null; if (c.ma?.en && c.ma.period >= 1) { maVals = this.computeMA(obvVals, c.ma.period); const maAll = maVals.filter(v => v != null && !isNaN(v)); if (maAll.length) { vMin = Math.min(vMin, ...maAll); vMax = Math.max(vMax, ...maAll); } } if (c.ema?.en && c.ema.period >= 1) { emaVals = this.computeEMA(obvVals, c.ema.period); const emaAll = emaVals.filter(v => v != null && !isNaN(v)); if (emaAll.length) { vMin = Math.min(vMin, ...emaAll); vMax = Math.max(vMax, ...emaAll); } } if (vMax === vMin) vMax = vMin + 1; this.ctx.setLineDash([]); const obvColor = c.obv?.color ?? c.color ?? '#ffeb3b'; const obvLw = (c.obv?.lineWidth != null && c.obv.lineWidth >= 1 && c.obv.lineWidth <= 4) ? c.obv.lineWidth : 2; this.ctx.strokeStyle = obvColor; this.ctx.lineWidth = obvLw; drawIndicatorLineScaled(obvVals, vMin, vMax, subBandBottom - subBandH, subBandBottom); if (maVals) { this.ctx.strokeStyle = c.ma.color || '#e91e63'; this.ctx.lineWidth = (c.ma.lineWidth != null && c.ma.lineWidth >= 1 && c.ma.lineWidth <= 4) ? c.ma.lineWidth : 2; drawIndicatorLineScaled(maVals, vMin, vMax, subBandBottom - subBandH, subBandBottom); } if (emaVals) { this.ctx.strokeStyle = c.ema.color || '#9c27b0'; this.ctx.lineWidth = (c.ema.lineWidth != null && c.ema.lineWidth >= 1 && c.ema.lineWidth <= 4) ? c.ema.lineWidth : 2; drawIndicatorLineScaled(emaVals, vMin, vMax, subBandBottom - subBandH, subBandBottom); } } },
            { key: 'subCci', draw: () => { const c = this.activeIndicators.subCci; if (!c) return; const period = c.period ?? c.length ?? 9; const vals = this.computeCCI(this.candles, period); this.ctx.strokeStyle = c.color || '#ffeb3b'; this.ctx.lineWidth = (c.lineWidth != null && c.lineWidth >= 1 && c.lineWidth <= 4) ? c.lineWidth : 2; this.ctx.setLineDash([]); drawIndicatorLineScaled(vals, -200, 200, subBandBottom - subBandH, subBandBottom); } },
            { key: 'subWr', draw: () => { const c = this.activeIndicators.subWr; if (!c) return; const period = c.period ?? 14; const vals = this.computeWR(this.candles, period); this.ctx.strokeStyle = c.color || '#ffeb3b'; this.ctx.lineWidth = (c.lineWidth != null && c.lineWidth >= 1 && c.lineWidth <= 4) ? c.lineWidth : 2; this.ctx.setLineDash([]); drawIndicatorLineScaled(vals, -100, 0, subBandBottom - subBandH, subBandBottom); } },
            { key: 'subMfi', draw: () => { const c = this.activeIndicators.subMfi; if (!c || !c.lines?.length) return; c.lines.forEach(line => { if (!line || !line.en || line.period < 2) return; const vals = this.computeMFI(this.candles, this.volumeData, line.period); this.ctx.strokeStyle = line.color || '#ff9800'; this.ctx.lineWidth = (line.lineWidth != null && line.lineWidth >= 1 && line.lineWidth <= 4) ? line.lineWidth : 2; this.ctx.setLineDash([]); drawIndicatorLineScaled(vals, 0, 100, subBandBottom - subBandH, subBandBottom); }); } },
            { key: 'subKdj', draw: () => { const c = this.activeIndicators.subKdj; if (!c) return; const calcPeriod = c.calcPeriod ?? (typeof c.k === 'number' ? c.k : 9), ma2 = c.ma2 ?? (typeof c.d === 'number' ? c.d : 3); const { k: kArr, d: dArr, j: jArr } = this.computeKDJ(this.candles, calcPeriod, ma2); this.ctx.setLineDash([]); if (c.k?.en || typeof c.k === 'number') { this.ctx.strokeStyle = (typeof c.k === 'object' && c.k) ? (c.k.color || '#e91e63') : (c.color || '#2196f3'); this.ctx.lineWidth = (typeof c.k === 'object' && c.k?.lineWidth != null && c.k.lineWidth >= 1 && c.k.lineWidth <= 4) ? c.k.lineWidth : 1; drawIndicatorLineScaled(kArr, 0, 100, subBandBottom - subBandH, subBandBottom); } if (c.d?.en) { this.ctx.strokeStyle = c.d.color || '#9c27b0'; this.ctx.lineWidth = (c.d.lineWidth != null && c.d.lineWidth >= 1 && c.d.lineWidth <= 4) ? c.d.lineWidth : 1; drawIndicatorLineScaled(dArr, 0, 100, subBandBottom - subBandH, subBandBottom); } if (c.j?.en) { this.ctx.strokeStyle = c.j.color || '#ffeb3b'; this.ctx.lineWidth = (c.j.lineWidth != null && c.j.lineWidth >= 1 && c.j.lineWidth <= 4) ? c.j.lineWidth : 1; drawIndicatorLineScaled(jArr, 0, 100, subBandBottom - subBandH, subBandBottom); } } },
            { key: 'subStochRsi', draw: () => { const c = this.activeIndicators.subStochRsi; if (!c) return; const rsi = this.computeRSI(this.candles.map(x => x.close), c.rsiPeriod ?? 14); const smoothK = c.smoothK ?? 3, smoothD = c.smoothD ?? 3; const { k: kArr, d: dArr } = this.computeStochRSIKD(rsi, c.stochPeriod ?? 14, smoothK, smoothD); this.ctx.setLineDash([]); if (c.k?.en) { this.ctx.strokeStyle = c.k.color || '#e91e63'; this.ctx.lineWidth = (c.k.lineWidth != null && c.k.lineWidth >= 1 && c.k.lineWidth <= 4) ? c.k.lineWidth : 2; drawIndicatorLineScaled(kArr, 0, 100, subBandBottom - subBandH, subBandBottom); } else if (c.color && typeof c.k !== 'object') { const vals = this.computeStochRSI(rsi, c.stochPeriod ?? 14); this.ctx.strokeStyle = c.color || '#e91e63'; this.ctx.lineWidth = 2; drawIndicatorLineScaled(vals, 0, 100, subBandBottom - subBandH, subBandBottom); } if (c.d?.en) { this.ctx.strokeStyle = c.d.color || '#9c27b0'; this.ctx.lineWidth = (c.d.lineWidth != null && c.d.lineWidth >= 1 && c.d.lineWidth <= 4) ? c.d.lineWidth : 2; drawIndicatorLineScaled(dArr, 0, 100, subBandBottom - subBandH, subBandBottom); } } },
            { key: 'subDmi', draw: () => { const c = this.activeIndicators.subDmi; if (!c) return; const period = c.period ?? 14; const { plus, minus, adx } = this.computeDMIWithADX(this.candles, period); this.ctx.setLineDash([]); const plusEn = c.plus?.en ?? (typeof c.plus !== 'object' && c.colorPlus); if (plusEn) { this.ctx.strokeStyle = (c.plus && typeof c.plus === 'object') ? (c.plus.color || '#e91e63') : (c.colorPlus || '#4caf50'); this.ctx.lineWidth = (c.plus?.lineWidth != null && c.plus.lineWidth >= 1 && c.plus.lineWidth <= 4) ? c.plus.lineWidth : 2; drawIndicatorLineScaled(plus, 0, 100, subBandBottom - subBandH, subBandBottom); } if (c.minus?.en || (typeof c.minus !== 'object' && c.colorMinus)) { this.ctx.strokeStyle = (c.minus && typeof c.minus === 'object') ? (c.minus.color || '#9c27b0') : (c.colorMinus || '#f44336'); this.ctx.lineWidth = (c.minus?.lineWidth != null && c.minus.lineWidth >= 1 && c.minus.lineWidth <= 4) ? c.minus.lineWidth : 2; drawIndicatorLineScaled(minus, 0, 100, subBandBottom - subBandH, subBandBottom); } if (c.adx?.en) { this.ctx.strokeStyle = c.adx.color || '#ffeb3b'; this.ctx.lineWidth = (c.adx.lineWidth != null && c.adx.lineWidth >= 1 && c.adx.lineWidth <= 4) ? c.adx.lineWidth : 2; drawIndicatorLineScaled(adx, 0, 100, subBandBottom - subBandH, subBandBottom); } } },
            { key: 'subMtm', draw: () => { const c = this.activeIndicators.subMtm; if (!c) return; const period = c.period ?? 14, source = c.source || 'close'; const vals = this.computeMTM(this.candles, period, source); const all = vals.filter(v => v != null && !isNaN(v)); const vMin = all.length ? Math.min(...all) : -1, vMax = all.length ? Math.max(...all) : 1; this.ctx.strokeStyle = c.color || '#ffeb3b'; this.ctx.lineWidth = (c.lineWidth != null && c.lineWidth >= 1 && c.lineWidth <= 4) ? c.lineWidth : 2; this.ctx.setLineDash([]); drawIndicatorLineScaled(vals, vMin, vMax, subBandBottom - subBandH, subBandBottom); } },
            { key: 'subEmv', draw: () => { const c = this.activeIndicators.subEmv; if (!c) return; const period = c.period ?? 14, divisor = c.divisor ?? 10000; const vals = this.computeEMV(this.candles, period, divisor); const all = vals.filter(v => v != null && !isNaN(v)); const vMin = all.length ? Math.min(...all) : -1, vMax = all.length ? Math.max(...all) : 1; this.ctx.strokeStyle = c.color || '#ffeb3b'; this.ctx.lineWidth = (c.lineWidth != null && c.lineWidth >= 1 && c.lineWidth <= 4) ? c.lineWidth : 2; this.ctx.setLineDash([]); drawIndicatorLineScaled(vals, vMin, vMax, subBandBottom - subBandH, subBandBottom); } }
        ];
        subIndicators.forEach(({ key, draw }) => {
            if (!this.activeIndicators[key]) return;
            draw();
            subBandBottom -= subBandH;
        });
    }

    processOrderBookData(data, dailyVolume, volumePercentage, exchange, market) {
        const threshold = dailyVolume * (volumePercentage / 100);
        const result = {
            dailyVolume: dailyVolume,
            currentPrice: null,
            bidDensity: null,
            askDensity: null
        };
        try {
            if (exchange === 'binance') {
                if (!data?.bids || !data?.asks) return null;
                const bestBid = parseFloat(data.bids[0][0]);
                const bestAsk = parseFloat(data.asks[0][0]);
                result.currentPrice = (bestBid + bestAsk) / 2;
                let maxBidVolume = 0;
                let maxBidPrice = 0;
                let currentBidVolume = 0;
                for (const [priceStr, amountStr] of data.bids) {
                    const price = parseFloat(priceStr);
                    const amount = parseFloat(amountStr);
                    currentBidVolume += price * amount;
                    if (currentBidVolume > maxBidVolume) {
                        maxBidVolume = currentBidVolume;
                        maxBidPrice = price;
                    }
                }
                let maxAskVolume = 0;
                let maxAskPrice = 0;
                let currentAskVolume = 0;
                for (const [priceStr, amountStr] of data.asks) {
                    const price = parseFloat(priceStr);
                    const amount = parseFloat(amountStr);
                    currentAskVolume += price * amount;
                    if (currentAskVolume > maxAskVolume) {
                        maxAskVolume = currentAskVolume;
                        maxAskPrice = price;
                    }
                }
                const bidCandidate = maxBidVolume > 0 ? {
                    price: maxBidPrice,
                    size: maxBidVolume,
                    distancePercent: ((maxBidPrice - result.currentPrice) / result.currentPrice) * 100
                } : null;
                const askCandidate = maxAskVolume > 0 ? {
                    price: maxAskPrice,
                    size: maxAskVolume,
                    distancePercent: ((maxAskPrice - result.currentPrice) / result.currentPrice) * 100
                } : null;
                if (maxBidVolume >= threshold) {
                    result.bidDensity = bidCandidate;
                }
                if (maxAskVolume >= threshold) {
                    result.askDensity = askCandidate;
                }
                // Fallback: если порог не достигнут, все равно показываем максимальные скопления
                if (!result.bidDensity && bidCandidate) result.bidDensity = bidCandidate;
                if (!result.askDensity && askCandidate) result.askDensity = askCandidate;
            } else if (exchange === 'bybit') {
                if (!data?.result || Number(data?.retCode) !== 0) return null;
                const bids = data.result.b || [];
                const asks = data.result.a || [];
                if (bids.length === 0 || asks.length === 0) return null;
                const bestBid = parseFloat(bids[0][0]);
                const bestAsk = parseFloat(asks[0][0]);
                result.currentPrice = (bestBid + bestAsk) / 2;
                let maxBidVolume = 0;
                let maxBidPrice = 0;
                let currentBidVolume = 0;
                for (const [priceStr, amountStr] of bids) {
                    const price = parseFloat(priceStr);
                    const amount = parseFloat(amountStr);
                    currentBidVolume += price * amount;
                    if (currentBidVolume > maxBidVolume) {
                        maxBidVolume = currentBidVolume;
                        maxBidPrice = price;
                    }
                }
                let maxAskVolume = 0;
                let maxAskPrice = 0;
                let currentAskVolume = 0;
                for (const [priceStr, amountStr] of asks) {
                    const price = parseFloat(priceStr);
                    const amount = parseFloat(amountStr);
                    currentAskVolume += price * amount;
                    if (currentAskVolume > maxAskVolume) {
                        maxAskVolume = currentAskVolume;
                        maxAskPrice = price;
                    }
                }
                const bidCandidate = maxBidVolume > 0 ? {
                    price: maxBidPrice,
                    size: maxBidVolume,
                    distancePercent: ((maxBidPrice - result.currentPrice) / result.currentPrice) * 100
                } : null;
                const askCandidate = maxAskVolume > 0 ? {
                    price: maxAskPrice,
                    size: maxAskVolume,
                    distancePercent: ((maxAskPrice - result.currentPrice) / result.currentPrice) * 100
                } : null;
                if (maxBidVolume >= threshold) {
                    result.bidDensity = bidCandidate;
                }
                if (maxAskVolume >= threshold) {
                    result.askDensity = askCandidate;
                }
                // Fallback: если порог не достигнут, все равно показываем максимальные скопления
                if (!result.bidDensity && bidCandidate) result.bidDensity = bidCandidate;
                if (!result.askDensity && askCandidate) result.askDensity = askCandidate;
            }
            return result;
        } catch (error) {
            console.error('Error processing order book:', error);
            return null;
        }
    }

    async fetchDailyVolumeQuote(exchange, ticker, market) {
        try {
            if (exchange === 'binance') {
                const endpoint = market === 'futures'
                    ? `https://fapi.binance.com/fapi/v1/ticker/24hr?symbol=${ticker}`
                    : `https://api.binance.com/api/v3/ticker/24hr?symbol=${ticker}`;
                const r = await fetch(endpoint);
                const d = await r.json();
                const quote = parseFloat(d?.quoteVolume);
                return Number.isFinite(quote) ? quote : null;
            }
            if (exchange === 'bybit') {
                const category = market === 'futures' ? 'linear' : 'spot';
                const endpoint = `https://api.bybit.com/v5/market/tickers?category=${category}&symbol=${ticker}`;
                const r = await fetch(endpoint);
                const d = await r.json();
                const item = d?.result?.list?.[0];
                const turnover = parseFloat(item?.turnover24h);
                return Number.isFinite(turnover) ? turnover : null;
            }
            return null;
        } catch {
            return null;
        }
    }

    async updateDensityData() {
        const enabled = !!this.valuesConfig?.density?.enabled;
        if (!enabled) {
            this.densityData = null;
            return;
        }
        const ticker = (this.symbol || 'BTCUSDT').toUpperCase();
        const market = this.market || 'spot';
        const exchange = (this.exchangeName || 'Binance').toLowerCase().includes('bybit') ? 'bybit' : 'binance';
        const dailyVolume = await this.fetchDailyVolumeQuote(exchange, ticker, market);
        if (!dailyVolume || dailyVolume <= 0) {
            this.densityData = null;
            this.draw();
            return;
        }
        try {
            let endpoint = '';
            if (exchange === 'binance') {
                endpoint = market === 'futures'
                    ? `https://fapi.binance.com/fapi/v1/depth?symbol=${ticker}&limit=${this.densityDepth}`
                    : `https://api.binance.com/api/v3/depth?symbol=${ticker}&limit=${this.densityDepth}`;
            } else {
                const category = market === 'futures' ? 'linear' : 'spot';
                endpoint = `https://api.bybit.com/v5/market/orderbook?category=${category}&limit=${this.densityDepth}&symbol=${ticker}`;
            }
            const response = await fetch(endpoint);
            const data = await response.json();
            this.densityData = this.processOrderBookData(
                data,
                dailyVolume,
                this.densityVolumePercentage,
                exchange,
                market
            );
        } catch (error) {
            console.error('Error fetching density data:', error);
            this.densityData = null;
        }
        this.draw();
    }

    startDensityUpdates() {
        if (this.densityUpdateTimer) clearInterval(this.densityUpdateTimer);
        if (!this.valuesConfig?.density?.enabled) return;
        this.updateDensityData();
        this.densityUpdateTimer = setInterval(() => this.updateDensityData(), 15000);
    }

    stopDensityUpdates() {
        if (this.densityUpdateTimer) {
            clearInterval(this.densityUpdateTimer);
            this.densityUpdateTimer = null;
        }
    }

    drawDensityValues() {
        if (!this.valuesConfig?.density?.enabled || !this.densityData) return;
        const levels = [];
        if (this.densityData.askDensity?.price != null) {
            levels.push({ side: 'ask', price: this.densityData.askDensity.price, size: this.densityData.askDensity.size });
        }
        if (this.densityData.bidDensity?.price != null) {
            levels.push({ side: 'bid', price: this.densityData.bidDensity.price, size: this.densityData.bidDensity.size });
        }
        if (levels.length === 0) return;

        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = Math.ceil(this.padding.left);
        const minY = Math.ceil(this.padding.top);
        const maxX = Math.floor(this.logicalWidth - this.padding.right);
        const maxY = Math.floor(this.padding.top + chartAreaHeight);
        const anchorX = Math.max(minX, Math.min(maxX, this.timeToX(this.endTime)));

        const formatSize = (n) => {
            if (!Number.isFinite(n)) return '0';
            if (n >= 1e9) return (n / 1e9).toFixed(1).replace(/\.0$/, '') + 'B';
            if (n >= 1e6) return (n / 1e6).toFixed(1).replace(/\.0$/, '') + 'M';
            if (n >= 1e3) return (n / 1e3).toFixed(0) + 'K';
            return n.toFixed(0);
        };

        this.ctx.save();
        this.ctx.beginPath();
        this.ctx.rect(minX, minY, maxX - minX, maxY - minY);
        this.ctx.clip();
        this.ctx.strokeStyle = this.valuesConfig?.density?.color || '#ff5252';
        this.ctx.lineWidth = 1.5;
        this.ctx.setLineDash([7, 5]);
        for (const level of levels) {
            const y = this.priceToY(level.price);
            if (y < minY || y > maxY) continue;
            this.ctx.beginPath();
            this.ctx.moveTo(anchorX, y);
            this.ctx.lineTo(maxX, y);
            this.ctx.stroke();
            this.ctx.setLineDash([]);
            this.ctx.fillStyle = this.valuesConfig?.density?.color || '#ff5252';
            this.ctx.beginPath();
            this.ctx.arc(anchorX, y, 2.2, 0, Math.PI * 2);
            this.ctx.fill();
            this.ctx.setLineDash([7, 5]);
        }
        this.ctx.restore();

        // Label boxes on the right (like screenshot)
        this.ctx.save();
        this.ctx.font = '12px sans-serif';
        this.ctx.textAlign = 'left';
        this.ctx.textBaseline = 'middle';
        for (const level of levels) {
            const y = this.priceToY(level.price);
            if (y < minY || y > maxY) continue;
            const sideTag = level.side === 'ask' ? 'BY-F' : 'OK-S';
            const text = `${sideTag} ${formatSize(level.size)} ${this.formatPrice(level.price)}`;
            const padX = 6;
            const boxH = 18;
            const textW = this.ctx.measureText(text).width;
            const boxW = textW + padX * 2;
            const boxX = Math.min(maxX + 6, this.logicalWidth - boxW - 6);
            const boxY = y - boxH / 2;
            this.ctx.fillStyle = 'rgba(33, 20, 20, 0.92)';
            this.ctx.strokeStyle = this.valuesConfig?.density?.color || '#ff5252';
            this.ctx.lineWidth = 1;
            this.ctx.fillRect(boxX, boxY, boxW, boxH);
            this.ctx.strokeRect(boxX, boxY, boxW, boxH);
            this.ctx.fillStyle = '#e0d8d8';
            this.ctx.fillText(text, boxX + padX, y);
        }
        this.ctx.restore();
    }

    calculateSupportResistanceLevels() {
        if (!Array.isArray(this.candles) || this.candles.length === 0) {
            return { supports: [], resistances: [], currentPrice: null };
        }
        const currentPrice = this.candles[this.candles.length - 1]?.close;
        if (currentPrice == null || Number.isNaN(currentPrice)) {
            return { supports: [], resistances: [], currentPrice: null };
        }
        const lowsSorted = this.candles
            .map(c => c.low)
            .filter(v => v != null && !Number.isNaN(v))
            .sort((a, b) => a - b);
        const highsSorted = this.candles
            .map(c => c.high)
            .filter(v => v != null && !Number.isNaN(v))
            .sort((a, b) => b - a);
        let support = null;
        for (const low of lowsSorted) {
            if (low < currentPrice) {
                support = low;
                break;
            }
        }
        let resistance = null;
        for (const high of highsSorted) {
            if (high > currentPrice) {
                resistance = high;
                break;
            }
        }
        return {
            supports: support == null ? [] : [support],
            resistances: resistance == null ? [] : [resistance],
            currentPrice
        };
    }

    drawSupportResistanceLevels() {
        const levelsCfg = this.levelsConfig || {};
        const drawSupport = !!levelsCfg.support?.enabled;
        const drawResistance = !!levelsCfg.resistance?.enabled;
        if (!drawSupport && !drawResistance) return;
        const { supports, resistances } = this.calculateSupportResistanceLevels();
        if (supports.length === 0 && resistances.length === 0) return;

        const chartAreaHeight = this.chartHeight - this.volumeHeight;
        const minX = Math.ceil(this.padding.left);
        const minY = Math.ceil(this.padding.top);
        const maxX = Math.floor(this.logicalWidth - this.padding.right);
        const maxY = Math.floor(this.padding.top + chartAreaHeight);

        this.ctx.save();
        this.ctx.beginPath();
        this.ctx.rect(minX, minY, maxX - minX, maxY - minY);
        this.ctx.clip();
        this.ctx.lineWidth = 1.5;
        this.ctx.setLineDash([8, 6]);

        if (drawSupport) {
            this.ctx.strokeStyle = levelsCfg.support?.color || '#00bcd4';
            supports.forEach(price => {
                const y = this.priceToY(price);
                if (y < minY || y > maxY) return;
                this.ctx.beginPath();
                this.ctx.moveTo(minX, y);
                this.ctx.lineTo(maxX, y);
                this.ctx.stroke();
            });
        }
        if (drawResistance) {
            this.ctx.strokeStyle = levelsCfg.resistance?.color || '#ff5252';
            resistances.forEach(price => {
                const y = this.priceToY(price);
                if (y < minY || y > maxY) return;
                this.ctx.beginPath();
                this.ctx.moveTo(minX, y);
                this.ctx.lineTo(maxX, y);
                this.ctx.stroke();
            });
        }
        this.ctx.setLineDash([]);
        this.ctx.restore();
    }
    
    draw() {
        if (!this.ctx || this.logicalWidth === 0 || this.logicalHeight === 0) {
            console.warn('Canvas not ready for drawing');
            return;
        }
        
        // Clear canvas
        this.ctx.fillStyle = '#2a2a2a';
        this.ctx.fillRect(0, 0, this.logicalWidth, this.logicalHeight);
        
        // Only draw if we have valid dimensions
        if (this.chartWidth <= 0 || this.chartHeight <= 0) {
            console.warn('Invalid chart dimensions:', this.chartWidth, this.chartHeight);
            return;
        }
        
        // Draw components
        try {
            this.drawGrid();
            // this.drawPriceLevels(); // Removed white dashed lines
            this.drawCandles();
            this.drawIndicators();
            this.drawSupportResistanceLevels();
            this.drawDensityValues();
            this.drawVolume();
            if (this.drawingsVisible) {
                this.drawRulerSelections();
                this.drawDrawnLines();
            }
            this.drawYAxis();
            this.drawXAxis();
            // this.drawWatermark(); // Removed PTB watermark
        } catch (error) {
            console.error('Error drawing chart:', error);
            console.error('Chart state:', {
                candles: this.candles?.length,
                chartWidth: this.chartWidth,
                chartHeight: this.chartHeight,
                canvasWidth: this.logicalWidth,
                canvasHeight: this.logicalHeight
            });
        }
    }
}

// Initialize chart when page loads
let chartInstance = null;

function initChart() {
    if (chartInstance) return;
    
    const canvas = document.getElementById('chartCanvas');
    if (!canvas) {
        console.error('Canvas element not found!');
        setTimeout(initChart, 50);
        return;
    }
    
    const container = canvas.parentElement;
    if (!container || container.clientWidth === 0 || container.clientHeight === 0) {
        // Retry if container doesn't have dimensions yet
        setTimeout(initChart, 50);
        return;
    }
    
    chartInstance = new CandlestickChart('chartCanvas');
    
    // Setup tool buttons
    setupToolButtons(chartInstance);
    
    // Setup timeframe buttons
    setupTimeframeButtons(chartInstance);
    
    // Setup indicators modal
    setupIndicatorsModal(chartInstance);
    
    // Setup values modal (плотности)
    setupValuesModal(chartInstance);
    
    // Setup levels modal (поддержка/сопротивление)
    setupLevelsModal(chartInstance);
    
    // Toggle visibility of drawing tools panel
    setupDrawingToggle();
    
    // Close WebSocket on page unload
    window.addEventListener('beforeunload', () => {
        if (chartInstance) {
            chartInstance.disconnectWebSocket();
        }
    });
}

function setupDrawingToggle() {
    const btn = document.getElementById('drawingToggleBtn');
    if (!btn || !chartInstance) return;
    if (chartInstance.drawingsVisible) btn.classList.add('active');
    btn.addEventListener('click', () => {
        chartInstance.drawingsVisible = !chartInstance.drawingsVisible;
        btn.setAttribute('aria-pressed', chartInstance.drawingsVisible ? 'true' : 'false');
        btn.classList.toggle('active', chartInstance.drawingsVisible);
        chartInstance.draw();
    });
}

function setupTimeframeButtons(chart) {
    const timeframeButtons = document.querySelectorAll('.timeframe-btn');
    const defaultInterval = '1d'; // Default interval (1 day)
    const intervalsOrder = ['3m', '5m', '15m', '30m', '1h', '2h', '4h', '1d'];
    
    // Set default active button
    timeframeButtons.forEach(btn => {
        if (btn.dataset.interval === defaultInterval) {
            btn.classList.add('active');
        }
    });
    
    function setActiveByInterval(interval) {
        timeframeButtons.forEach(b => {
            b.classList.toggle('active', b.dataset.interval === interval);
        });
    }
    
    function switchTimeframeByArrow(direction) {
        if (!chart) return;
        const current = (chart.interval || '1d').toLowerCase();
        const idx = intervalsOrder.indexOf(current);
        if (idx === -1) return;
        let nextIdx = direction === 'prev' ? idx - 1 : idx + 1;
        if (nextIdx < 0) nextIdx = 0;
        if (nextIdx >= intervalsOrder.length) nextIdx = intervalsOrder.length - 1;
        const newInterval = intervalsOrder[nextIdx];
        if (newInterval === current) return;
        setActiveByInterval(newInterval);
        chart.changeTimeframe(newInterval);
    }
    
    timeframeButtons.forEach(btn => {
        btn.addEventListener('click', () => {
            const interval = btn.dataset.interval;
            setActiveByInterval(interval);
            if (chart) chart.changeTimeframe(interval);
        });
    });
    
    // Переключение таймфреймов стрелками влево/вправо
    document.addEventListener('keydown', (e) => {
        if (e.key !== 'ArrowLeft' && e.key !== 'ArrowRight') return;
        const el = document.activeElement;
        if (el && (el.tagName === 'INPUT' || el.tagName === 'TEXTAREA' || el.isContentEditable)) return;
        e.preventDefault();
        switchTimeframeByArrow(e.key === 'ArrowLeft' ? 'prev' : 'next');
    });
}

function setupLevelsModal(chart) {
    const modal = document.getElementById('levelsModal');
    const btn = document.getElementById('levelsBtn');
    const closeBtn = document.getElementById('levelsModalClose');
    const saveBtn = document.getElementById('levelsSave');
    const resetBtn = document.getElementById('levelsReset');
    const titleEl = document.getElementById('levelsConfigTitle');
    if (!modal || !btn || !chart) return;

    const supportListItem = modal.querySelector('.levels-item[data-level="support"]');
    const resistanceListItem = modal.querySelector('.levels-item[data-level="resistance"]');
    const supportPanel = document.getElementById('levelSupportConfig');
    const resistancePanel = document.getElementById('levelResistanceConfig');
    const supportListCheckbox = document.getElementById('levelSupportEn');
    const resistanceListCheckbox = document.getElementById('levelResistanceEn');
    const supportPanelCheckbox = document.getElementById('levelSupportPanelEn');
    const resistancePanelCheckbox = document.getElementById('levelResistancePanelEn');
    const supportColor = document.getElementById('levelSupportColor');
    const resistanceColor = document.getElementById('levelResistanceColor');

    function syncCheckboxes() {
        if (supportListCheckbox) supportListCheckbox.checked = !!supportPanelCheckbox?.checked;
        if (resistanceListCheckbox) resistanceListCheckbox.checked = !!resistancePanelCheckbox?.checked;
    }

    function showLevel(level) {
        const isSupport = level === 'support';
        if (supportPanel) supportPanel.style.display = isSupport ? '' : 'none';
        if (resistancePanel) resistancePanel.style.display = isSupport ? 'none' : '';
        supportListItem?.classList.toggle('selected', isSupport);
        resistanceListItem?.classList.toggle('selected', !isSupport);
        if (titleEl) titleEl.textContent = isSupport ? 'Поддержки' : 'Сопротивления';
    }

    function syncFromChart() {
        const cfg = chart.levelsConfig || {};
        if (supportPanelCheckbox) supportPanelCheckbox.checked = !!cfg.support?.enabled;
        if (resistancePanelCheckbox) resistancePanelCheckbox.checked = !!cfg.resistance?.enabled;
        if (supportColor) supportColor.value = cfg.support?.color || '#00bcd4';
        if (resistanceColor) resistanceColor.value = cfg.resistance?.color || '#ff5252';
        syncCheckboxes();
        showLevel('support');
    }

    function closeModal() {
        modal.classList.remove('open');
        btn.classList.remove('active');
    }

    function openModal() {
        syncFromChart();
        modal.classList.add('open');
        btn.classList.add('active');
    }

    function saveFromModal() {
        chart.levelsConfig = {
            support: { enabled: !!supportPanelCheckbox?.checked, color: supportColor?.value || '#00bcd4' },
            resistance: { enabled: !!resistancePanelCheckbox?.checked, color: resistanceColor?.value || '#ff5252' }
        };
        chart.draw();
        closeModal();
    }

    function resetModal() {
        if (supportPanelCheckbox) supportPanelCheckbox.checked = false;
        if (resistancePanelCheckbox) resistancePanelCheckbox.checked = false;
        if (supportColor) supportColor.value = '#00bcd4';
        if (resistanceColor) resistanceColor.value = '#ff5252';
        syncCheckboxes();
        chart.levelsConfig = {
            support: { enabled: false, color: '#00bcd4' },
            resistance: { enabled: false, color: '#ff5252' }
        };
        chart.draw();
    }

    supportListItem?.addEventListener('click', (e) => {
        if (e.target instanceof HTMLInputElement && e.target.type === 'checkbox') return;
        showLevel('support');
    });
    resistanceListItem?.addEventListener('click', (e) => {
        if (e.target instanceof HTMLInputElement && e.target.type === 'checkbox') return;
        showLevel('resistance');
    });
    supportListCheckbox?.addEventListener('change', () => {
        if (supportPanelCheckbox) supportPanelCheckbox.checked = !!supportListCheckbox.checked;
    });
    resistanceListCheckbox?.addEventListener('change', () => {
        if (resistancePanelCheckbox) resistancePanelCheckbox.checked = !!resistanceListCheckbox.checked;
    });
    supportPanelCheckbox?.addEventListener('change', syncCheckboxes);
    resistancePanelCheckbox?.addEventListener('change', syncCheckboxes);

    btn.addEventListener('click', openModal);
    closeBtn?.addEventListener('click', closeModal);
    saveBtn?.addEventListener('click', saveFromModal);
    resetBtn?.addEventListener('click', resetModal);
    modal.addEventListener('click', (e) => {
        if (e.target === modal) closeModal();
    });
}

function setupValuesModal(chart) {
    const modal = document.getElementById('valuesModal');
    const btn = document.getElementById('valuesBtn');
    const closeBtn = document.getElementById('valuesModalClose');
    const saveBtn = document.getElementById('valuesSave');
    const resetBtn = document.getElementById('valuesReset');
    const titleEl = document.getElementById('valuesConfigTitle');
    if (!modal || !btn || !chart) return;

    const densityItem = modal.querySelector('.values-item[data-value="density"]');
    const densityListCheckbox = document.getElementById('valueDensityEn');
    const densityPanelCheckbox = document.getElementById('valueDensityPanelEn');
    const densityColor = document.getElementById('valueDensityColor');

    function syncCheckboxes() {
        const enabled = !!densityPanelCheckbox?.checked;
        if (densityListCheckbox) densityListCheckbox.checked = enabled;
    }

    function syncFromChart() {
        const cfg = chart.valuesConfig || {};
        if (densityPanelCheckbox) densityPanelCheckbox.checked = !!cfg.density?.enabled;
        if (densityColor) densityColor.value = cfg.density?.color || '#ff5252';
        syncCheckboxes();
        densityItem?.classList.add('selected');
        if (titleEl) titleEl.textContent = 'Плотности';
    }

    function closeModal() {
        modal.classList.remove('open');
        btn.classList.remove('active');
    }

    function openModal() {
        syncFromChart();
        modal.classList.add('open');
        btn.classList.add('active');
    }

    function saveFromModal() {
        chart.valuesConfig = {
            density: {
                enabled: !!densityPanelCheckbox?.checked,
                color: densityColor?.value || '#ff5252'
            }
        };
        if (chart.valuesConfig.density.enabled) chart.startDensityUpdates();
        else {
            chart.stopDensityUpdates();
            chart.densityData = null;
        }
        chart.draw();
        closeModal();
    }

    function resetModal() {
        if (densityPanelCheckbox) densityPanelCheckbox.checked = false;
        if (densityColor) densityColor.value = '#ff5252';
        syncCheckboxes();
        chart.valuesConfig = { density: { enabled: false, color: '#ff5252' } };
        chart.stopDensityUpdates();
        chart.densityData = null;
        chart.draw();
    }

    densityItem?.addEventListener('click', () => densityItem.classList.add('selected'));
    densityListCheckbox?.addEventListener('change', () => {
        if (densityPanelCheckbox) densityPanelCheckbox.checked = !!densityListCheckbox.checked;
    });
    densityPanelCheckbox?.addEventListener('change', syncCheckboxes);

    btn.addEventListener('click', openModal);
    closeBtn?.addEventListener('click', closeModal);
    saveBtn?.addEventListener('click', saveFromModal);
    resetBtn?.addEventListener('click', resetModal);
    modal.addEventListener('click', (e) => {
        if (e.target === modal) closeModal();
    });
}

function setupIndicatorsModal(chart) {
    const modal = document.getElementById('indicatorsModal');
    const btn = document.getElementById('indicatorsBtn');
    const closeBtn = document.getElementById('indicatorsModalClose');
    const saveBtn = document.getElementById('indicatorsSave');
    const resetBtn = document.getElementById('indicatorsReset');
    const tabs = modal.querySelectorAll('.indicators-tab');
    
    if (!modal || !btn) return;
    
    const panelIds = { MA: 'maConfig', EMA: 'emaConfig', WMA: 'wmaConfig', BOLL: 'bollConfig', VWAP: 'vwapConfig', MACD: 'macdConfig', RSI: 'rsiConfig', TRIX: 'trixConfig', SUPER: 'superConfig', SAR: 'sarConfig' };
    const subPanelIds = { VOL: 'subVolConfig', MACD: 'subMacdConfig', RSI: 'subRsiConfig', MFI: 'subMfiConfig', KDJ: 'subKdjConfig', OBV: 'subObvConfig', CCI: 'subCciConfig', StochRSI: 'subStochRsiConfig', WR: 'subWrConfig', DMI: 'subDmiConfig', MTM: 'subMtmConfig', EMV: 'subEmvConfig' };
    const subTitles = { VOL: 'Vol - Объём', MACD: 'Схождение/расхождение средних скользящих', RSI: 'RSI - Индекс относительной силы', MFI: 'MFI - Индекс потока средств', KDJ: 'KDJ - Стохастический индикатор', OBV: 'OBV - Сбалансированный объем', CCI: 'CCI - Индекс товарного канала', StochRSI: 'StochRSI - Стохастический RSI', WR: 'WR - Wm%R', DMI: 'DMI - Индекс направленного движения', MTM: 'MTM - Индекс импульса', EMV: 'EMV - Значение легкости движения' };
    
    const mainContent = document.getElementById('indicatorsMainContent');
    const subContent = document.getElementById('indicatorsSubContent');
    const mainConfig = document.getElementById('mainIndicatorsConfig');
    const subConfig = document.getElementById('subIndicatorsConfig');
    const subConfigTitle = document.getElementById('subIndicatorsConfigTitle');
    
    function openModal() {
        modal.classList.add('open');
        syncModalFromChart();
        const activeTab = modal.querySelector('.indicators-tab.active');
        const tabName = activeTab ? activeTab.getAttribute('data-tab') : 'main';
        if (tabName === 'sub') {
            if (mainContent) mainContent.style.display = 'none';
            if (subContent) subContent.style.display = 'flex';
            const subSelected = modal.querySelector('.sub-indicator-item.selected');
            const subId = subSelected ? (subSelected.getAttribute('data-sub') || subSelected.querySelector('input')?.value) : 'VOL';
            subConfig?.querySelectorAll('.sub-indicator-panel').forEach(panel => {
                panel.style.display = (panel.id === subPanelIds[subId]) ? '' : 'none';
            });
            if (subConfigTitle) subConfigTitle.textContent = subTitles[subId] || subId;
        } else {
            if (mainContent) mainContent.style.display = 'flex';
            if (subContent) subContent.style.display = 'none';
            const selected = modal.querySelector('.indicator-item.selected');
            const id = selected ? (selected.getAttribute('data-indicator') || selected.querySelector('input')?.value) : 'MA';
            mainConfig?.querySelectorAll('.indicator-config-panel').forEach(panel => {
                if (!panel.classList.contains('sub-indicator-panel')) panel.style.display = (panel.id === panelIds[id]) ? '' : 'none';
            });
        }
    }
    
    function closeModal() {
        modal.classList.remove('open');
    }
    
    function syncModalFromChart() {
        const defColors = ['#ffeb3b', '#e91e63', '#9c27b0', '#f44336', '#4caf50', '#ff9800'];
        ['ma', 'ema', 'wma'].forEach(prefix => {
            const list = chart.activeIndicators[prefix] || [];
            const key = prefix.toUpperCase().slice(0, 2) + (prefix === 'wma' ? 'A' : prefix === 'ema' ? 'A' : '');
            const idPrefix = prefix;
            for (let i = 1; i <= 6; i++) {
                const en = document.getElementById(idPrefix + i + 'en');
                const period = document.getElementById(idPrefix + i + 'period');
                const source = document.getElementById(idPrefix + i + 'source');
                const color = document.getElementById(idPrefix + i + 'color');
                if (!en || !period) continue;
                const cfg = list[i - 1];
                if (cfg) {
                    en.checked = true;
                    period.value = cfg.period;
                    if (source) source.value = cfg.source || 'close';
                    if (color) color.value = cfg.color || defColors[i - 1];
                } else {
                    en.checked = false;
                    period.value = i <= 3 ? (i === 1 ? 7 : i === 2 ? 25 : 99) : 0;
                    if (source) source.value = 'close';
                    if (color) color.value = defColors[i - 1];
                }
            }
        });
        const b = chart.activeIndicators.boll;
        const el = id => document.getElementById(id);
        if (el('bollEn')) el('bollEn').checked = !!b;
        if (b) {
            if (el('bollPeriod')) el('bollPeriod').value = b.period ?? 20;
            if (el('bollStd')) el('bollStd').value = b.std ?? 2;
            if (el('bollColorUpper')) el('bollColorUpper').value = b.colorUpper || '#2196f3';
            if (el('bollColorMid')) el('bollColorMid').value = b.colorMid || '#ff9800';
            if (el('bollColorLower')) el('bollColorLower').value = b.colorLower || '#2196f3';
        }
        const v = chart.activeIndicators.vwap;
        if (el('vwapEn')) el('vwapEn').checked = !!v;
        if (v && el('vwapColor')) el('vwapColor').value = v.color || '#00bcd4';
        const s = chart.activeIndicators.sar;
        if (el('sarEn')) el('sarEn').checked = !!s;
        if (s) {
            if (el('sarStep')) el('sarStep').value = s.step ?? 0.02;
            if (el('sarMax')) el('sarMax').value = s.max ?? 0.2;
            if (el('sarColor')) el('sarColor').value = s.color || '#f44336';
        }
        const m = chart.activeIndicators.macd;
        if (el('macdEn')) el('macdEn').checked = !!m;
        if (m) {
            if (el('macdFast')) el('macdFast').value = m.fast ?? 12;
            if (el('macdSlow')) el('macdSlow').value = m.slow ?? 26;
            if (el('macdSignal')) el('macdSignal').value = m.signal ?? 9;
            if (el('macdColorMacd')) el('macdColorMacd').value = m.colorMacd ?? '#2196f3';
            if (el('macdColorSignal')) el('macdColorSignal').value = m.colorSignal ?? '#ff9800';
        }
        const r = chart.activeIndicators.rsi;
        if (el('rsiEn')) el('rsiEn').checked = !!r;
        if (r) {
            if (el('rsiPeriod')) el('rsiPeriod').value = r.period ?? 14;
            if (el('rsiColor')) el('rsiColor').value = r.color ?? '#9c27b0';
        }
        const t = chart.activeIndicators.trix;
        if (el('trixEn')) el('trixEn').checked = !!t;
        if (t) {
            if (el('trixPeriod')) el('trixPeriod').value = t.period ?? 15;
            if (el('trixColor')) el('trixColor').value = t.color ?? '#00bcd4';
        }
        const u = chart.activeIndicators.super;
        if (el('superEn')) el('superEn').checked = !!u;
        if (u) {
            if (el('superPeriod')) el('superPeriod').value = u.period ?? 10;
            if (el('superMultiplier')) el('superMultiplier').value = u.multiplier ?? 3;
            if (el('superColor')) el('superColor').value = u.color ?? '#f44336';
        }
        const subVol = chart.activeIndicators.subVol;
        if (el('subVolMavol1en')) el('subVolMavol1en').checked = subVol?.mavol1?.en ?? false;
        if (subVol?.mavol1) {
            if (el('subVolMavol1period')) el('subVolMavol1period').value = subVol.mavol1.period ?? '';
            if (el('subVolMavol1width')) el('subVolMavol1width').value = subVol.mavol1.lineWidth ?? 2;
            if (el('subVolMavol1color')) el('subVolMavol1color').value = subVol.mavol1.color ?? '#03a9f4';
        } else {
            if (el('subVolMavol1period')) el('subVolMavol1period').value = '';
        }
        if (el('subVolMavol2en')) el('subVolMavol2en').checked = subVol?.mavol2?.en ?? false;
        if (subVol?.mavol2) {
            if (el('subVolMavol2period')) el('subVolMavol2period').value = subVol.mavol2.period ?? '';
            if (el('subVolMavol2width')) el('subVolMavol2width').value = subVol.mavol2.lineWidth ?? 2;
            if (el('subVolMavol2color')) el('subVolMavol2color').value = subVol.mavol2.color ?? '#e91e63';
        } else {
            if (el('subVolMavol2period')) el('subVolMavol2period').value = '';
        }
        if (subVol && el('subVolLong')) el('subVolLong').value = subVol.long ?? 'close';
        if (subVol && el('subVolShort')) el('subVolShort').value = subVol.short ?? 'close';
        const subMacd = chart.activeIndicators.subMacd;
        if (subMacd) {
            if (el('subMacdFast')) el('subMacdFast').value = subMacd.fast ?? '';
            if (el('subMacdSlow')) el('subMacdSlow').value = subMacd.slow ?? '';
            if (el('subMacdSignal')) el('subMacdSignal').value = subMacd.signal ?? '';
            if (el('subMacdDeaEn')) el('subMacdDeaEn').checked = subMacd.dea?.en !== false;
            if (el('subMacdDeaWidth')) el('subMacdDeaWidth').value = subMacd.dea?.lineWidth ?? 2;
            if (el('subMacdDeaColor')) el('subMacdDeaColor').value = subMacd.dea?.color ?? '#e91e63';
            if (el('subMacdDifEn')) el('subMacdDifEn').checked = subMacd.dif?.en !== false;
            if (el('subMacdDifWidth')) el('subMacdDifWidth').value = subMacd.dif?.lineWidth ?? 2;
            if (el('subMacdDifColor')) el('subMacdDifColor').value = subMacd.dif?.color ?? '#9c27b0';
            if (el('subMacdHistEn')) el('subMacdHistEn').checked = subMacd.hist?.en !== false;
            if (el('subMacdHistWidth')) el('subMacdHistWidth').value = subMacd.hist?.lineWidth ?? 2;
            if (el('subMacdHistColor')) el('subMacdHistColor').value = subMacd.hist?.color ?? '#607d8b';
            if (el('subMacdLongGrowStyle')) el('subMacdLongGrowStyle').value = subMacd.longGrowStyle ?? 'hollow';
            if (el('subMacdLongGrowColor')) el('subMacdLongGrowColor').value = subMacd.longGrowColor ?? '#26a69a';
            if (el('subMacdLongFallStyle')) el('subMacdLongFallStyle').value = subMacd.longFallStyle ?? 'filled';
            if (el('subMacdLongFallColor')) el('subMacdLongFallColor').value = subMacd.longFallColor ?? '#26a69a';
            if (el('subMacdShortGrowStyle')) el('subMacdShortGrowStyle').value = subMacd.shortGrowStyle ?? 'hollow';
            if (el('subMacdShortGrowColor')) el('subMacdShortGrowColor').value = subMacd.shortGrowColor ?? '#ef5350';
            if (el('subMacdShortFallStyle')) el('subMacdShortFallStyle').value = subMacd.shortFallStyle ?? 'filled';
            if (el('subMacdShortFallColor')) el('subMacdShortFallColor').value = subMacd.shortFallColor ?? '#ef5350';
        } else {
            if (el('subMacdFast')) el('subMacdFast').value = '';
            if (el('subMacdSlow')) el('subMacdSlow').value = '';
            if (el('subMacdSignal')) el('subMacdSignal').value = '';
            if (el('subMacdDeaEn')) el('subMacdDeaEn').checked = false;
            if (el('subMacdDifEn')) el('subMacdDifEn').checked = false;
            if (el('subMacdHistEn')) el('subMacdHistEn').checked = false;
        }
        const subRsi = chart.activeIndicators.subRsi;
        const subRsiLines = subRsi?.lines;
        if (subRsiLines && Array.isArray(subRsiLines)) {
            [1, 2, 3].forEach(i => {
                const l = subRsiLines[i - 1];
                if (l) {
                    if (el('subRsiLine' + i + 'en')) el('subRsiLine' + i + 'en').checked = l.en !== false;
                    if (el('subRsiLine' + i + 'period')) el('subRsiLine' + i + 'period').value = l.period ?? (i === 1 ? 6 : i === 2 ? 12 : 24);
                    if (el('subRsiLine' + i + 'width')) el('subRsiLine' + i + 'width').value = (l.lineWidth ?? 2);
                    if (el('subRsiLine' + i + 'color')) el('subRsiLine' + i + 'color').value = l.color ?? (i === 1 ? '#e91e63' : i === 2 ? '#9c27b0' : '#ffeb3b');
                }
            });
        } else if (subRsi && (subRsi.period != null || subRsi.color)) {
            if (el('subRsiLine1en')) el('subRsiLine1en').checked = true;
            if (el('subRsiLine1period')) el('subRsiLine1period').value = subRsi.period ?? 14;
            if (el('subRsiLine1width')) el('subRsiLine1width').value = subRsi.lineWidth ?? 2;
            if (el('subRsiLine1color')) el('subRsiLine1color').value = subRsi.color ?? '#9c27b0';
            if (el('subRsiLine2en')) el('subRsiLine2en').checked = false;
            if (el('subRsiLine3en')) el('subRsiLine3en').checked = false;
        } else {
            if (el('subRsiLine1en')) el('subRsiLine1en').checked = false;
            if (el('subRsiLine2en')) el('subRsiLine2en').checked = false;
            if (el('subRsiLine3en')) el('subRsiLine3en').checked = false;
        }
        const subMfi = chart.activeIndicators.subMfi;
        const subMfiLines = subMfi?.lines;
        if (subMfiLines && Array.isArray(subMfiLines)) {
            [1, 2, 3].forEach(i => {
                const l = subMfiLines[i - 1];
                if (l) {
                    if (el('subMfiLine' + i + 'en')) el('subMfiLine' + i + 'en').checked = l.en !== false;
                    if (el('subMfiLine' + i + 'period')) el('subMfiLine' + i + 'period').value = l.period ?? (i === 1 ? 7 : i === 2 ? 14 : 21);
                    if (el('subMfiLine' + i + 'width')) el('subMfiLine' + i + 'width').value = (l.lineWidth ?? 2);
                    if (el('subMfiLine' + i + 'color')) el('subMfiLine' + i + 'color').value = l.color ?? (i === 1 ? '#ff4081' : i === 2 ? '#9c27b0' : '#ffc107');
                }
            });
        } else if (subMfi && (subMfi.period != null || subMfi.color)) {
            if (el('subMfiLine1en')) el('subMfiLine1en').checked = true;
            if (el('subMfiLine1period')) el('subMfiLine1period').value = subMfi.period ?? 14;
            if (el('subMfiLine1width')) el('subMfiLine1width').value = subMfi.lineWidth ?? 2;
            if (el('subMfiLine1color')) el('subMfiLine1color').value = subMfi.color ?? '#ff9800';
            if (el('subMfiLine2en')) el('subMfiLine2en').checked = false;
            if (el('subMfiLine3en')) el('subMfiLine3en').checked = false;
        } else {
            if (el('subMfiLine1en')) el('subMfiLine1en').checked = false;
            if (el('subMfiLine2en')) el('subMfiLine2en').checked = false;
            if (el('subMfiLine3en')) el('subMfiLine3en').checked = false;
        }
        const subKdj = chart.activeIndicators.subKdj;
        if (subKdj) {
            if (subKdj.calcPeriod != null || (subKdj.k && typeof subKdj.k === 'object')) {
                if (el('subKdjCalcPeriod')) el('subKdjCalcPeriod').value = subKdj.calcPeriod ?? 9;
                if (el('subKdjMa1')) el('subKdjMa1').value = subKdj.ma1 ?? 3;
                if (el('subKdjMa2')) el('subKdjMa2').value = subKdj.ma2 ?? 3;
                if (el('subKdjKEn')) el('subKdjKEn').checked = subKdj.k?.en !== false;
                if (subKdj.k && typeof subKdj.k === 'object') { if (el('subKdjKWidth')) el('subKdjKWidth').value = subKdj.k.lineWidth ?? 1; if (el('subKdjKColor')) el('subKdjKColor').value = subKdj.k.color ?? '#e91e63'; }
                if (el('subKdjDEn')) el('subKdjDEn').checked = subKdj.d?.en !== false;
                if (subKdj.d && typeof subKdj.d === 'object') { if (el('subKdjDWidth')) el('subKdjDWidth').value = subKdj.d.lineWidth ?? 1; if (el('subKdjDColor')) el('subKdjDColor').value = subKdj.d.color ?? '#9c27b0'; }
                if (el('subKdjJEn')) el('subKdjJEn').checked = subKdj.j?.en !== false;
                if (subKdj.j && typeof subKdj.j === 'object') { if (el('subKdjJWidth')) el('subKdjJWidth').value = subKdj.j.lineWidth ?? 1; if (el('subKdjJColor')) el('subKdjJColor').value = subKdj.j.color ?? '#ffeb3b'; }
            } else {
                if (el('subKdjCalcPeriod')) el('subKdjCalcPeriod').value = subKdj.k ?? 9;
                if (el('subKdjMa1')) el('subKdjMa1').value = 3;
                if (el('subKdjMa2')) el('subKdjMa2').value = subKdj.d ?? 3;
                if (el('subKdjKEn')) el('subKdjKEn').checked = true;
                if (el('subKdjKColor')) el('subKdjKColor').value = subKdj.color ?? '#2196f3';
                if (el('subKdjDEn')) el('subKdjDEn').checked = false;
                if (el('subKdjJEn')) el('subKdjJEn').checked = false;
            }
        } else {
            if (el('subKdjKEn')) el('subKdjKEn').checked = false;
            if (el('subKdjDEn')) el('subKdjDEn').checked = false;
            if (el('subKdjJEn')) el('subKdjJEn').checked = false;
        }
        const subObv = chart.activeIndicators.subObv;
        if (subObv) {
            const obvCfg = subObv.obv || (subObv.color != null ? { color: subObv.color, lineWidth: 2 } : null);
            if (obvCfg) { if (el('subObvWidth')) el('subObvWidth').value = obvCfg.lineWidth ?? 2; if (el('subObvColor')) el('subObvColor').value = obvCfg.color ?? '#ffeb3b'; }
            if (el('subObvMaEn')) el('subObvMaEn').checked = !!subObv.ma?.en;
            if (subObv.ma) { if (el('subObvMaPeriod')) el('subObvMaPeriod').value = subObv.ma.period ?? 7; if (el('subObvMaWidth')) el('subObvMaWidth').value = subObv.ma.lineWidth ?? 2; if (el('subObvMaColor')) el('subObvMaColor').value = subObv.ma.color ?? '#e91e63'; }
            if (el('subObvEmaEn')) el('subObvEmaEn').checked = !!subObv.ema?.en;
            if (subObv.ema) { if (el('subObvEmaPeriod')) el('subObvEmaPeriod').value = subObv.ema.period ?? 7; if (el('subObvEmaWidth')) el('subObvEmaWidth').value = subObv.ema.lineWidth ?? 2; if (el('subObvEmaColor')) el('subObvEmaColor').value = subObv.ema.color ?? '#9c27b0'; }
        } else {
            if (el('subObvMaEn')) el('subObvMaEn').checked = false;
            if (el('subObvEmaEn')) el('subObvEmaEn').checked = false;
        }
        const subCci = chart.activeIndicators.subCci;
        if (subCci) {
            if (el('subCciLength')) el('subCciLength').value = subCci.period ?? subCci.length ?? 9;
            if (el('subCciWidth')) el('subCciWidth').value = subCci.lineWidth ?? 2;
            if (el('subCciColor')) el('subCciColor').value = subCci.color ?? '#ffeb3b';
        }
        const subStochRsi = chart.activeIndicators.subStochRsi;
        if (subStochRsi) {
            if (el('subStochRsiRsiLength')) el('subStochRsiRsiLength').value = subStochRsi.rsiPeriod ?? 14;
            if (el('subStochRsiStochLength')) el('subStochRsiStochLength').value = subStochRsi.stochPeriod ?? 14;
            if (el('subStochRsiSmoothK')) el('subStochRsiSmoothK').value = subStochRsi.smoothK ?? 3;
            if (el('subStochRsiSmoothD')) el('subStochRsiSmoothD').value = subStochRsi.smoothD ?? 3;
            if (subStochRsi.k && typeof subStochRsi.k === 'object') {
                if (el('subStochRsiKEn')) el('subStochRsiKEn').checked = subStochRsi.k.en !== false;
                if (el('subStochRsiKWidth')) el('subStochRsiKWidth').value = subStochRsi.k.lineWidth ?? 2;
                if (el('subStochRsiKColor')) el('subStochRsiKColor').value = subStochRsi.k.color ?? '#e91e63';
            } else {
                if (el('subStochRsiKEn')) el('subStochRsiKEn').checked = true;
                if (el('subStochRsiKColor')) el('subStochRsiKColor').value = subStochRsi.color ?? '#e91e63';
            }
            if (subStochRsi.d && typeof subStochRsi.d === 'object') {
                if (el('subStochRsiDEn')) el('subStochRsiDEn').checked = subStochRsi.d.en !== false;
                if (el('subStochRsiDWidth')) el('subStochRsiDWidth').value = subStochRsi.d.lineWidth ?? 2;
                if (el('subStochRsiDColor')) el('subStochRsiDColor').value = subStochRsi.d.color ?? '#9c27b0';
            } else {
                if (el('subStochRsiDEn')) el('subStochRsiDEn').checked = false;
            }
        } else {
            if (el('subStochRsiKEn')) el('subStochRsiKEn').checked = false;
            if (el('subStochRsiDEn')) el('subStochRsiDEn').checked = false;
        }
        const subWr = chart.activeIndicators.subWr;
        if (subWr) {
            if (el('subWrLength')) el('subWrLength').value = subWr.period ?? 14;
            if (el('subWrWidth')) el('subWrWidth').value = subWr.lineWidth ?? 2;
            if (el('subWrColor')) el('subWrColor').value = subWr.color ?? '#ffeb3b';
        }
        const subDmi = chart.activeIndicators.subDmi;
        if (subDmi) {
            if (el('subDmiLength')) el('subDmiLength').value = subDmi.period ?? 14;
            if (subDmi.plus && typeof subDmi.plus === 'object') {
                if (el('subDmiPlusEn')) el('subDmiPlusEn').checked = subDmi.plus.en !== false;
                if (el('subDmiPlusWidth')) el('subDmiPlusWidth').value = subDmi.plus.lineWidth ?? 2;
                if (el('subDmiColorPlus')) el('subDmiColorPlus').value = subDmi.plus.color ?? '#e91e63';
            } else {
                if (el('subDmiPlusEn')) el('subDmiPlusEn').checked = true;
                if (el('subDmiColorPlus')) el('subDmiColorPlus').value = subDmi.colorPlus ?? '#4caf50';
            }
            if (subDmi.minus && typeof subDmi.minus === 'object') {
                if (el('subDmiMinusEn')) el('subDmiMinusEn').checked = subDmi.minus.en !== false;
                if (el('subDmiMinusWidth')) el('subDmiMinusWidth').value = subDmi.minus.lineWidth ?? 2;
                if (el('subDmiColorMinus')) el('subDmiColorMinus').value = subDmi.minus.color ?? '#9c27b0';
            } else {
                if (el('subDmiMinusEn')) el('subDmiMinusEn').checked = true;
                if (el('subDmiColorMinus')) el('subDmiColorMinus').value = subDmi.colorMinus ?? '#f44336';
            }
            if (subDmi.adx && typeof subDmi.adx === 'object') {
                if (el('subDmiAdxEn')) el('subDmiAdxEn').checked = subDmi.adx.en !== false;
                if (el('subDmiAdxWidth')) el('subDmiAdxWidth').value = subDmi.adx.lineWidth ?? 2;
                if (el('subDmiColorAdx')) el('subDmiColorAdx').value = subDmi.adx.color ?? '#ffeb3b';
            } else {
                if (el('subDmiAdxEn')) el('subDmiAdxEn').checked = false;
            }
        } else {
            if (el('subDmiPlusEn')) el('subDmiPlusEn').checked = false;
            if (el('subDmiMinusEn')) el('subDmiMinusEn').checked = false;
            if (el('subDmiAdxEn')) el('subDmiAdxEn').checked = false;
        }
        const subMtm = chart.activeIndicators.subMtm;
        if (subMtm) {
            if (el('subMtmLength')) el('subMtmLength').value = subMtm.period ?? 14;
            if (el('subMtmSource')) el('subMtmSource').value = subMtm.source ?? 'close';
            if (el('subMtmWidth')) el('subMtmWidth').value = subMtm.lineWidth ?? 2;
            if (el('subMtmColor')) el('subMtmColor').value = subMtm.color ?? '#ffeb3b';
        }
        const subEmv = chart.activeIndicators.subEmv;
        if (subEmv) {
            if (el('subEmvLength')) el('subEmvLength').value = subEmv.period ?? 14;
            if (el('subEmvWidth')) el('subEmvWidth').value = subEmv.lineWidth ?? 2;
            if (el('subEmvColor')) el('subEmvColor').value = subEmv.color ?? '#ffeb3b';
            if (el('subEmvDivisor')) el('subEmvDivisor').value = subEmv.divisor ?? 10000;
        }
        const subListMap = { VOL: 'subVol', MACD: 'subMacd', RSI: 'subRsi', MFI: 'subMfi', KDJ: 'subKdj', OBV: 'subObv', CCI: 'subCci', StochRSI: 'subStochRsi', WR: 'subWr', DMI: 'subDmi', MTM: 'subMtm', EMV: 'subEmv' };
        document.querySelectorAll('.sub-indicator-item').forEach(item => {
            const dataSub = item.getAttribute('data-sub');
            const key = subListMap[dataSub];
            const cb = item.querySelector('input[type="checkbox"]');
            if (cb && key) cb.checked = !!chart.activeIndicators[key];
        });
        document.querySelectorAll('.line-thickness-picker').forEach(p => { if (typeof syncLineThicknessTrigger === 'function') syncLineThicknessTrigger(p); });
    }
    
    const maDefaults = [
        { en: true, period: 7, source: 'close', color: '#ffeb3b' },
        { en: true, period: 25, source: 'close', color: '#e91e63' },
        { en: true, period: 99, source: 'close', color: '#9c27b0' },
        { en: false, period: 0, source: 'close', color: '#f44336' },
        { en: false, period: 0, source: 'close', color: '#4caf50' },
        { en: false, period: 0, source: 'close', color: '#ff9800' }
    ];
    function applyDefaults() {
        ['ma', 'ema', 'wma'].forEach(prefix => {
            maDefaults.forEach((d, idx) => {
                const i = idx + 1;
                const en = document.getElementById(prefix + i + 'en');
                const period = document.getElementById(prefix + i + 'period');
                const source = document.getElementById(prefix + i + 'source');
                const color = document.getElementById(prefix + i + 'color');
                if (en) en.checked = d.en;
                if (period) period.value = d.period;
                if (source) source.value = d.source;
                if (color) color.value = d.color;
            });
        });
        const el = id => document.getElementById(id);
        if (el('bollEn')) el('bollEn').checked = true;
        if (el('bollPeriod')) el('bollPeriod').value = 20;
        if (el('bollStd')) el('bollStd').value = 2;
        if (el('bollColorUpper')) el('bollColorUpper').value = '#2196f3';
        if (el('bollColorMid')) el('bollColorMid').value = '#ff9800';
        if (el('bollColorLower')) el('bollColorLower').value = '#2196f3';
        if (el('vwapEn')) el('vwapEn').checked = true;
        if (el('vwapColor')) el('vwapColor').value = '#00bcd4';
        if (el('sarEn')) el('sarEn').checked = true;
        if (el('sarStep')) el('sarStep').value = 0.02;
        if (el('sarMax')) el('sarMax').value = 0.2;
        if (el('sarColor')) el('sarColor').value = '#f44336';
    }
    
    function readMaEmaWma(prefix) {
        const out = [];
        for (let i = 1; i <= 6; i++) {
            const en = document.getElementById(prefix + i + 'en');
            const periodEl = document.getElementById(prefix + i + 'period');
            const sourceEl = document.getElementById(prefix + i + 'source');
            const widthEl = document.getElementById(prefix + i + 'width');
            const colorEl = document.getElementById(prefix + i + 'color');
            if (!en?.checked || !periodEl) continue;
            const period = parseInt(periodEl.value, 10);
            if (isNaN(period) || period < 1) continue;
            const lineWidth = widthEl ? Math.max(1, Math.min(4, parseInt(widthEl.value, 10) || 2)) : 2;
            out.push({
                period,
                source: sourceEl ? sourceEl.value : 'close',
                lineWidth,
                color: colorEl ? colorEl.value : '#ffeb3b'
            });
        }
        return out;
    }
    
    function saveFromModal() {
        chart.activeIndicators.ma = readMaEmaWma('ma');
        chart.activeIndicators.ema = readMaEmaWma('ema');
        chart.activeIndicators.wma = readMaEmaWma('wma');
        const bollEn = document.getElementById('bollEn');
        const bollPeriodEl = document.getElementById('bollPeriod');
        const bollStdEl = document.getElementById('bollStd');
        if (bollEn?.checked && bollPeriodEl && bollStdEl) {
            const period = parseInt(bollPeriodEl.value, 10);
            chart.activeIndicators.boll = (period >= 2) ? {
                period,
                std: parseFloat(bollStdEl.value) || 2,
                colorUpper: document.getElementById('bollColorUpper')?.value || '#2196f3',
                colorMid: document.getElementById('bollColorMid')?.value || '#ff9800',
                colorLower: document.getElementById('bollColorLower')?.value || '#2196f3'
            } : null;
        } else {
            chart.activeIndicators.boll = null;
        }
        const vwapEn = document.getElementById('vwapEn');
        const vwapColorEl = document.getElementById('vwapColor');
        chart.activeIndicators.vwap = (vwapEn?.checked && vwapColorEl) ? { color: vwapColorEl.value } : null;
        const sarEn = document.getElementById('sarEn');
        const sarStepEl = document.getElementById('sarStep');
        const sarMaxEl = document.getElementById('sarMax');
        if (sarEn?.checked && sarStepEl && sarMaxEl) {
            const step = parseFloat(sarStepEl.value);
            chart.activeIndicators.sar = (step > 0) ? {
                step,
                max: parseFloat(sarMaxEl.value) || 0.2,
                color: document.getElementById('sarColor')?.value || '#f44336'
            } : null;
        } else {
            chart.activeIndicators.sar = null;
        }
        const macdEn = document.getElementById('macdEn');
        const macdFastEl = document.getElementById('macdFast');
        const macdSlowEl = document.getElementById('macdSlow');
        const macdSignalEl = document.getElementById('macdSignal');
        if (macdEn?.checked && macdFastEl && macdSlowEl && macdSignalEl) {
            const fast = parseInt(macdFastEl.value, 10) || 12;
            const slow = parseInt(macdSlowEl.value, 10) || 26;
            const signal = parseInt(macdSignalEl.value, 10) || 9;
            chart.activeIndicators.macd = (slow > fast) ? {
                fast, slow, signal,
                colorMacd: document.getElementById('macdColorMacd')?.value || '#2196f3',
                colorSignal: document.getElementById('macdColorSignal')?.value || '#ff9800'
            } : null;
        } else {
            chart.activeIndicators.macd = null;
        }
        const rsiEn = document.getElementById('rsiEn');
        const rsiPeriodEl = document.getElementById('rsiPeriod');
        if (rsiEn?.checked && rsiPeriodEl) {
            const period = parseInt(rsiPeriodEl.value, 10) || 14;
            chart.activeIndicators.rsi = (period >= 2) ? {
                period,
                color: document.getElementById('rsiColor')?.value || '#9c27b0'
            } : null;
        } else {
            chart.activeIndicators.rsi = null;
        }
        const trixEn = document.getElementById('trixEn');
        const trixPeriodEl = document.getElementById('trixPeriod');
        if (trixEn?.checked && trixPeriodEl) {
            const period = parseInt(trixPeriodEl.value, 10) || 15;
            chart.activeIndicators.trix = (period >= 1) ? {
                period,
                color: document.getElementById('trixColor')?.value || '#00bcd4'
            } : null;
        } else {
            chart.activeIndicators.trix = null;
        }
        const superEn = document.getElementById('superEn');
        const superPeriodEl = document.getElementById('superPeriod');
        const superMultEl = document.getElementById('superMultiplier');
        if (superEn?.checked && superPeriodEl && superMultEl) {
            const period = parseInt(superPeriodEl.value, 10) || 10;
            const multiplier = parseFloat(superMultEl.value) || 3;
            chart.activeIndicators.super = (period >= 1 && multiplier > 0) ? {
                period, multiplier,
                color: document.getElementById('superColor')?.value || '#f44336'
            } : null;
        } else {
            chart.activeIndicators.super = null;
        }
        const subVolMavol1en = document.getElementById('subVolMavol1en');
        const subVolMavol2en = document.getElementById('subVolMavol2en');
        if (subVolMavol1en || subVolMavol2en) {
            const mavol1 = (subVolMavol1en?.checked) ? {
                en: true,
                period: parseInt(document.getElementById('subVolMavol1period')?.value, 10) || 7,
                lineWidth: Math.max(1, Math.min(4, parseInt(document.getElementById('subVolMavol1width')?.value, 10) || 2)),
                color: document.getElementById('subVolMavol1color')?.value || '#03a9f4'
            } : null;
            const mavol2 = (subVolMavol2en?.checked) ? {
                en: true,
                period: parseInt(document.getElementById('subVolMavol2period')?.value, 10) || 14,
                lineWidth: Math.max(1, Math.min(4, parseInt(document.getElementById('subVolMavol2width')?.value, 10) || 2)),
                color: document.getElementById('subVolMavol2color')?.value || '#e91e63'
            } : null;
            chart.activeIndicators.subVol = (mavol1 || mavol2) ? {
                mavol1: mavol1,
                mavol2: mavol2,
                long: document.getElementById('subVolLong')?.value || 'close',
                short: document.getElementById('subVolShort')?.value || 'close'
            } : null;
        }
        const subMacdFastEl = document.getElementById('subMacdFast');
        const subMacdSlowEl = document.getElementById('subMacdSlow');
        const subMacdSignalEl = document.getElementById('subMacdSignal');
        if (subMacdFastEl && subMacdSlowEl && subMacdSignalEl) {
            const fast = parseInt(subMacdFastEl.value, 10) || 12;
            const slow = parseInt(subMacdSlowEl.value, 10) || 26;
            const signal = parseInt(subMacdSignalEl.value, 10) || 9;
            const deaEn = document.getElementById('subMacdDeaEn')?.checked;
            const difEn = document.getElementById('subMacdDifEn')?.checked;
            const histEn = document.getElementById('subMacdHistEn')?.checked;
            if (slow > fast && (deaEn || difEn || histEn)) {
                const el = id => document.getElementById(id);
                chart.activeIndicators.subMacd = {
                    fast, slow, signal,
                    dea: deaEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subMacdDeaWidth')?.value, 10) || 2)), color: el('subMacdDeaColor')?.value || '#e91e63' } : null,
                    dif: difEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subMacdDifWidth')?.value, 10) || 2)), color: el('subMacdDifColor')?.value || '#9c27b0' } : null,
                    hist: histEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subMacdHistWidth')?.value, 10) || 2)), color: el('subMacdHistColor')?.value || '#607d8b' } : null,
                    longGrowStyle: el('subMacdLongGrowStyle')?.value || 'hollow',
                    longGrowColor: el('subMacdLongGrowColor')?.value || '#26a69a',
                    longFallStyle: el('subMacdLongFallStyle')?.value || 'filled',
                    longFallColor: el('subMacdLongFallColor')?.value || '#26a69a',
                    shortGrowStyle: el('subMacdShortGrowStyle')?.value || 'hollow',
                    shortGrowColor: el('subMacdShortGrowColor')?.value || '#ef5350',
                    shortFallStyle: el('subMacdShortFallStyle')?.value || 'filled',
                    shortFallColor: el('subMacdShortFallColor')?.value || '#ef5350'
                };
            } else {
                chart.activeIndicators.subMacd = null;
            }
        } else {
            chart.activeIndicators.subMacd = null;
        }
        const el = id => document.getElementById(id);
        const subRsiLines = [
            { en: el('subRsiLine1en')?.checked, period: parseInt(el('subRsiLine1period')?.value, 10) || 6, lineWidth: Math.max(1, Math.min(4, parseInt(el('subRsiLine1width')?.value, 10) || 2)), color: el('subRsiLine1color')?.value || '#e91e63' },
            { en: el('subRsiLine2en')?.checked, period: parseInt(el('subRsiLine2period')?.value, 10) || 12, lineWidth: Math.max(1, Math.min(4, parseInt(el('subRsiLine2width')?.value, 10) || 2)), color: el('subRsiLine2color')?.value || '#9c27b0' },
            { en: el('subRsiLine3en')?.checked, period: parseInt(el('subRsiLine3period')?.value, 10) || 24, lineWidth: Math.max(1, Math.min(4, parseInt(el('subRsiLine3width')?.value, 10) || 2)), color: el('subRsiLine3color')?.value || '#ffeb3b' }
        ];
        const anySubRsi = subRsiLines.some(l => l.en && l.period >= 2);
        chart.activeIndicators.subRsi = anySubRsi ? { lines: subRsiLines } : null;
        const subMfiLines = [
            { en: el('subMfiLine1en')?.checked, period: parseInt(el('subMfiLine1period')?.value, 10) || 7, lineWidth: Math.max(1, Math.min(4, parseInt(el('subMfiLine1width')?.value, 10) || 2)), color: el('subMfiLine1color')?.value || '#ff4081' },
            { en: el('subMfiLine2en')?.checked, period: parseInt(el('subMfiLine2period')?.value, 10) || 14, lineWidth: Math.max(1, Math.min(4, parseInt(el('subMfiLine2width')?.value, 10) || 2)), color: el('subMfiLine2color')?.value || '#9c27b0' },
            { en: el('subMfiLine3en')?.checked, period: parseInt(el('subMfiLine3period')?.value, 10) || 21, lineWidth: Math.max(1, Math.min(4, parseInt(el('subMfiLine3width')?.value, 10) || 2)), color: el('subMfiLine3color')?.value || '#ffc107' }
        ];
        const anySubMfi = subMfiLines.some(l => l.en && l.period >= 2);
        chart.activeIndicators.subMfi = anySubMfi ? { lines: subMfiLines } : null;
        const subKdjCalcPeriod = parseInt(el('subKdjCalcPeriod')?.value, 10) || 9;
        const subKdjMa1 = parseInt(el('subKdjMa1')?.value, 10) || 3;
        const subKdjMa2 = parseInt(el('subKdjMa2')?.value, 10) || 3;
        const kEn = el('subKdjKEn')?.checked, dEn = el('subKdjDEn')?.checked, jEn = el('subKdjJEn')?.checked;
        const anyKdj = kEn || dEn || jEn;
        if (anyKdj && subKdjCalcPeriod >= 2) {
            chart.activeIndicators.subKdj = {
                calcPeriod: subKdjCalcPeriod,
                ma1: subKdjMa1,
                ma2: subKdjMa2,
                k: kEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subKdjKWidth')?.value, 10) || 1)), color: el('subKdjKColor')?.value || '#e91e63' } : null,
                d: dEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subKdjDWidth')?.value, 10) || 1)), color: el('subKdjDColor')?.value || '#9c27b0' } : null,
                j: jEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subKdjJWidth')?.value, 10) || 1)), color: el('subKdjJColor')?.value || '#ffeb3b' } : null
            };
        } else chart.activeIndicators.subKdj = null;
        const obvListCb = document.querySelector('.sub-indicator-item[data-sub="OBV"] input[type="checkbox"]');
        if (obvListCb?.checked) {
            chart.activeIndicators.subObv = {
                obv: { lineWidth: Math.max(1, Math.min(4, parseInt(el('subObvWidth')?.value, 10) || 2)), color: el('subObvColor')?.value || '#ffeb3b' },
                ma: el('subObvMaEn')?.checked ? { en: true, period: parseInt(el('subObvMaPeriod')?.value, 10) || 7, lineWidth: Math.max(1, Math.min(4, parseInt(el('subObvMaWidth')?.value, 10) || 2)), color: el('subObvMaColor')?.value || '#e91e63' } : null,
                ema: el('subObvEmaEn')?.checked ? { en: true, period: parseInt(el('subObvEmaPeriod')?.value, 10) || 7, lineWidth: Math.max(1, Math.min(4, parseInt(el('subObvEmaWidth')?.value, 10) || 2)), color: el('subObvEmaColor')?.value || '#9c27b0' } : null
            };
        } else chart.activeIndicators.subObv = null;
        const cciListCb = document.querySelector('.sub-indicator-item[data-sub="CCI"] input[type="checkbox"]');
        if (cciListCb?.checked) {
            const length = parseInt(el('subCciLength')?.value, 10) || 9;
            chart.activeIndicators.subCci = length >= 2 ? {
                period: length,
                lineWidth: Math.max(1, Math.min(4, parseInt(el('subCciWidth')?.value, 10) || 2)),
                color: el('subCciColor')?.value || '#ffeb3b'
            } : null;
        } else chart.activeIndicators.subCci = null;
        const stochRsiKEn = el('subStochRsiKEn')?.checked, stochRsiDEn = el('subStochRsiDEn')?.checked;
        if (stochRsiKEn || stochRsiDEn) {
            const rsiLen = parseInt(el('subStochRsiRsiLength')?.value, 10) || 14, stochLen = parseInt(el('subStochRsiStochLength')?.value, 10) || 14;
            const smoothK = parseInt(el('subStochRsiSmoothK')?.value, 10) || 3, smoothD = parseInt(el('subStochRsiSmoothD')?.value, 10) || 3;
            chart.activeIndicators.subStochRsi = {
                rsiPeriod: rsiLen,
                stochPeriod: stochLen,
                smoothK,
                smoothD,
                k: stochRsiKEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subStochRsiKWidth')?.value, 10) || 2)), color: el('subStochRsiKColor')?.value || '#e91e63' } : null,
                d: stochRsiDEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subStochRsiDWidth')?.value, 10) || 2)), color: el('subStochRsiDColor')?.value || '#9c27b0' } : null
            };
        } else chart.activeIndicators.subStochRsi = null;
        const wrListCb = document.querySelector('.sub-indicator-item[data-sub="WR"] input[type="checkbox"]');
        if (wrListCb?.checked) {
            const length = parseInt(el('subWrLength')?.value, 10) || 14;
            chart.activeIndicators.subWr = length >= 2 ? {
                period: length,
                lineWidth: Math.max(1, Math.min(4, parseInt(el('subWrWidth')?.value, 10) || 2)),
                color: el('subWrColor')?.value || '#ffeb3b'
            } : null;
        } else chart.activeIndicators.subWr = null;
        const dmiPlusEn = el('subDmiPlusEn')?.checked, dmiMinusEn = el('subDmiMinusEn')?.checked, dmiAdxEn = el('subDmiAdxEn')?.checked;
        if (dmiPlusEn || dmiMinusEn || dmiAdxEn) {
            const period = parseInt(el('subDmiLength')?.value, 10) || 14;
            chart.activeIndicators.subDmi = period >= 2 ? {
                period,
                plus: dmiPlusEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subDmiPlusWidth')?.value, 10) || 2)), color: el('subDmiColorPlus')?.value || '#e91e63' } : null,
                minus: dmiMinusEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subDmiMinusWidth')?.value, 10) || 2)), color: el('subDmiColorMinus')?.value || '#9c27b0' } : null,
                adx: dmiAdxEn ? { en: true, lineWidth: Math.max(1, Math.min(4, parseInt(el('subDmiAdxWidth')?.value, 10) || 2)), color: el('subDmiColorAdx')?.value || '#ffeb3b' } : null
            } : null;
        } else chart.activeIndicators.subDmi = null;
        const mtmListCb = document.querySelector('.sub-indicator-item[data-sub="MTM"] input[type="checkbox"]');
        if (mtmListCb?.checked) {
            const period = parseInt(el('subMtmLength')?.value, 10) || 14;
            chart.activeIndicators.subMtm = period >= 1 ? {
                period,
                source: el('subMtmSource')?.value || 'close',
                lineWidth: Math.max(1, Math.min(4, parseInt(el('subMtmWidth')?.value, 10) || 2)),
                color: el('subMtmColor')?.value || '#ffeb3b'
            } : null;
        } else chart.activeIndicators.subMtm = null;
        const emvListCb = document.querySelector('.sub-indicator-item[data-sub="EMV"] input[type="checkbox"]');
        if (emvListCb?.checked) {
            const period = parseInt(el('subEmvLength')?.value, 10) || 14;
            const divisor = parseInt(el('subEmvDivisor')?.value, 10) || 10000;
            chart.activeIndicators.subEmv = period >= 2 ? {
                period,
                divisor: (divisor > 0) ? divisor : 10000,
                lineWidth: Math.max(1, Math.min(4, parseInt(el('subEmvWidth')?.value, 10) || 2)),
                color: el('subEmvColor')?.value || '#ffeb3b'
            } : null;
        } else chart.activeIndicators.subEmv = null;
        chart.draw();
        closeModal();
    }
    
    btn.addEventListener('click', openModal);
    closeBtn?.addEventListener('click', closeModal);
    modal.addEventListener('click', (e) => {
        if (e.target === modal) closeModal();
    });
    saveBtn?.addEventListener('click', saveFromModal);
    resetBtn?.addEventListener('click', () => {
        chart.activeIndicators.ma = [];
        chart.activeIndicators.ema = [];
        chart.activeIndicators.wma = [];
        chart.activeIndicators.boll = null;
        chart.activeIndicators.vwap = null;
        chart.activeIndicators.sar = null;
        chart.activeIndicators.macd = null;
        chart.activeIndicators.rsi = null;
        chart.activeIndicators.trix = null;
        chart.activeIndicators.super = null;
        // Очистить форму без подстановки значений по умолчанию
        ['ma', 'ema', 'wma'].forEach(prefix => {
            for (let i = 1; i <= 6; i++) {
                const en = document.getElementById(prefix + i + 'en');
                const period = document.getElementById(prefix + i + 'period');
                if (en) en.checked = false;
                if (period) period.value = '0';
            }
        });
        const el = id => document.getElementById(id);
        if (el('bollEn')) el('bollEn').checked = false;
        if (el('vwapEn')) el('vwapEn').checked = false;
        if (el('sarEn')) el('sarEn').checked = false;
        if (el('macdEn')) el('macdEn').checked = false;
        if (el('rsiEn')) el('rsiEn').checked = false;
        if (el('trixEn')) el('trixEn').checked = false;
        if (el('superEn')) el('superEn').checked = false;
        chart.activeIndicators.subVol = null;
        chart.activeIndicators.subMacd = null;
        chart.activeIndicators.subRsi = null;
        chart.activeIndicators.subMfi = null;
        chart.activeIndicators.subKdj = null;
        chart.activeIndicators.subObv = null;
        chart.activeIndicators.subCci = null;
        chart.activeIndicators.subStochRsi = null;
        chart.activeIndicators.subWr = null;
        chart.activeIndicators.subDmi = null;
        chart.activeIndicators.subMtm = null;
        chart.activeIndicators.subEmv = null;
        document.querySelectorAll('.sub-indicator-item input[type="checkbox"]').forEach(cb => { cb.checked = false; });
        ['subRsiLine1en','subRsiLine2en','subRsiLine3en','subMfiLine1en','subMfiLine2en','subMfiLine3en','subKdjKEn','subKdjDEn','subKdjJEn','subObvMaEn','subObvEmaEn','subStochRsiKEn','subStochRsiDEn','subDmiPlusEn','subDmiMinusEn','subDmiAdxEn'].forEach(id => { const e = document.getElementById(id); if (e) e.checked = false; });
        chart.draw();
    });
    
    tabs.forEach(tab => {
        tab.addEventListener('click', () => {
            tabs.forEach(t => t.classList.remove('active'));
            tab.classList.add('active');
            const tabName = tab.getAttribute('data-tab');
            if (tabName === 'sub') {
                if (mainContent) mainContent.style.display = 'none';
                if (subContent) subContent.style.display = 'flex';
                const subSelected = document.querySelector('.sub-indicator-item.selected');
                const subId = subSelected ? (subSelected.getAttribute('data-sub') || subSelected.querySelector('input')?.value) : 'VOL';
                subConfig?.querySelectorAll('.sub-indicator-panel').forEach(panel => {
                    panel.style.display = (panel.id === subPanelIds[subId]) ? '' : 'none';
                });
                if (subConfigTitle) subConfigTitle.textContent = subTitles[subId] || subId;
            } else {
                if (mainContent) mainContent.style.display = 'flex';
                if (subContent) subContent.style.display = 'none';
                const selected = document.querySelector('.indicator-item.selected');
                const id = selected ? (selected.getAttribute('data-indicator') || selected.querySelector('input')?.value) : 'MA';
                mainConfig?.querySelectorAll('.indicator-config-panel').forEach(panel => {
                    if (!panel.classList.contains('sub-indicator-panel')) panel.style.display = (panel.id === panelIds[id]) ? '' : 'none';
                });
            }
        });
    });
    
    document.querySelectorAll('.sub-indicator-item').forEach(item => {
        item.addEventListener('click', (e) => {
            if (e.target.type === 'checkbox') {
                const dataSub = item.getAttribute('data-sub');
                const enIds = { VOL: ['subVolMavol1en', 'subVolMavol2en'], MACD: ['subMacdDeaEn', 'subMacdDifEn', 'subMacdHistEn'], RSI: ['subRsiLine1en', 'subRsiLine2en', 'subRsiLine3en'], MFI: ['subMfiLine1en', 'subMfiLine2en', 'subMfiLine3en'], KDJ: ['subKdjKEn', 'subKdjDEn', 'subKdjJEn'], OBV: [], CCI: [], StochRSI: ['subStochRsiKEn', 'subStochRsiDEn'], WR: [], DMI: ['subDmiPlusEn', 'subDmiMinusEn', 'subDmiAdxEn'], MTM: [], EMV: [] };
                const en = enIds[dataSub];
                const checked = e.target.checked;
                if (Array.isArray(en)) en.forEach(id => { const el = document.getElementById(id); if (el) el.checked = checked; });
                else if (en) { const el = document.getElementById(en); if (el) el.checked = checked; }
                return;
            }
            document.querySelectorAll('.sub-indicator-item').forEach(i => i.classList.remove('selected'));
            item.classList.add('selected');
            const subId = item.getAttribute('data-sub') || item.querySelector('input')?.value || 'VOL';
            subConfig?.querySelectorAll('.sub-indicator-panel').forEach(panel => {
                panel.style.display = (panel.id === subPanelIds[subId]) ? '' : 'none';
            });
            if (subConfigTitle) subConfigTitle.textContent = subTitles[subId] || subId;
        });
    });
    
    const titles = { MA: 'MA - Средняя скользящая', EMA: 'EMA - Экспоненциальная средняя', WMA: 'WMA - Взвешенная средняя', BOLL: 'BOLL - Полосы Боллинджера', VWAP: 'VWAP', MACD: 'MACD - Схождение/расхождение скользящих', RSI: 'RSI - Индекс относительной силы', TRIX: 'TRIX - Тройная экспоненциальная средняя', SUPER: 'SUPER - SuperTrend', SAR: 'SAR - Parabolic SAR' };
    
    function showPanelForIndicator(id) {
        mainConfig?.querySelectorAll('.indicator-config-panel').forEach(panel => {
            if (!panel.classList.contains('sub-indicator-panel')) {
                panel.style.display = (panel.id === panelIds[id]) ? '' : 'none';
            }
        });
        const title = document.getElementById('indicatorsConfigTitle');
        if (title) title.textContent = titles[id] || id + ' - Настройки';
    }
    
    modal.querySelectorAll('.indicator-item[data-indicator]').forEach(item => {
        item.addEventListener('click', (e) => {
            if (e.target.type === 'checkbox') return;
            modal.querySelectorAll('.indicator-item[data-indicator]').forEach(i => i.classList.remove('selected'));
            item.classList.add('selected');
            const id = item.getAttribute('data-indicator') || item.querySelector('input')?.value || 'MA';
            showPanelForIndicator(id);
        });
    });

    // Визуальный выбор толщины линии — показываем линии разной толщины вместо чисел
    function syncLineThicknessTrigger(picker) {
        const select = picker.querySelector('select.ma-line-width-select');
        const triggerPreview = picker.querySelector('.line-thickness-trigger .line-preview');
        if (!select || !triggerPreview) return;
        const v = select.value || '2';
        triggerPreview.className = 'line-preview lt-' + v;
    }
    document.querySelectorAll('.line-thickness-picker').forEach(picker => {
        syncLineThicknessTrigger(picker);
        const trigger = picker.querySelector('.line-thickness-trigger');
        const dropdown = picker.querySelector('.line-thickness-dropdown');
        const select = picker.querySelector('select.ma-line-width-select');
        if (!trigger || !dropdown || !select) return;
        trigger.addEventListener('click', (e) => {
            e.stopPropagation();
            const isOpen = picker.classList.toggle('open');
            if (isOpen) {
                document.querySelectorAll('.line-thickness-picker.open').forEach(p => {
                    if (p !== picker) p.classList.remove('open');
                });
            }
        });
        dropdown.querySelectorAll('.line-thickness-option').forEach(opt => {
            opt.addEventListener('click', (e) => {
                e.stopPropagation();
                const val = opt.getAttribute('data-value');
                if (val) {
                    select.value = val;
                    syncLineThicknessTrigger(picker);
                }
                picker.classList.remove('open');
            });
        });
    });
    document.addEventListener('click', () => {
        document.querySelectorAll('.line-thickness-picker.open').forEach(p => p.classList.remove('open'));
    });
}

function setupToolButtons(chart) {
    const alertBtn = document.querySelector('.tool-btn[title="Alert"]');
    const brushBtn = document.querySelector('.tool-btn[title="Brush"]');
    const horizontalLineBtn = document.querySelector('.tool-btn[title="Horizontal Line"]');
    const rectangleBtn = document.querySelector('.tool-btn[title="Rectangle"]');
    const rulerBtn = document.querySelector('.tool-btn[title="Ruler"]');
    const deleteBtn = document.querySelector('.tool-btn[title="Delete"]');
    
    function deactivateAlert() {
        if (alertBtn) alertBtn.classList.remove('active');
        if (chart) chart.setAlertMode?.(false);
    }
    
    // Delete button requires double click
    let deleteClickCount = 0;
    let deleteClickTimer = null;
    
    if (alertBtn) {
        alertBtn.addEventListener('click', () => {
            const isActive = chart.alertMode;
            chart.setAlertMode(!isActive);
            if (!isActive) {
                alertBtn.classList.add('active');
                if (brushBtn) brushBtn.classList.remove('active');
                if (horizontalLineBtn) horizontalLineBtn.classList.remove('active');
                if (rectangleBtn) rectangleBtn.classList.remove('active');
                if (rulerBtn) rulerBtn.classList.remove('active');
            } else {
                alertBtn.classList.remove('active');
            }
        });
    }
    
    if (brushBtn) {
        brushBtn.addEventListener('click', () => {
            const isActive = chart.drawingMode;
            chart.setDrawingMode(!isActive);
            if (!isActive) {
                brushBtn.classList.add('active');
                deactivateAlert();
                if (horizontalLineBtn) horizontalLineBtn.classList.remove('active');
                if (rectangleBtn) rectangleBtn.classList.remove('active');
                if (rulerBtn) rulerBtn.classList.remove('active');
            } else {
                brushBtn.classList.remove('active');
            }
        });
    }
    
    if (horizontalLineBtn) {
        horizontalLineBtn.addEventListener('click', () => {
            const isActive = chart.horizontalLineMode;
            chart.setHorizontalLineMode(!isActive);
            if (!isActive) {
                horizontalLineBtn.classList.add('active');
                if (brushBtn) brushBtn.classList.remove('active');
                deactivateAlert();
                if (rectangleBtn) rectangleBtn.classList.remove('active');
                if (rulerBtn) rulerBtn.classList.remove('active');
            } else {
                horizontalLineBtn.classList.remove('active');
            }
        });
    }
    
    if (rectangleBtn) {
        rectangleBtn.addEventListener('click', () => {
            // Toggle rectangle mode
            const isActive = chart.rectangleMode;
            chart.setRectangleMode(!isActive);
            
            // Update button appearance
            if (!isActive) {
                rectangleBtn.classList.add('active');
                if (brushBtn) brushBtn.classList.remove('active');
                if (horizontalLineBtn) horizontalLineBtn.classList.remove('active');
                if (rulerBtn) rulerBtn.classList.remove('active');
            } else {
                rectangleBtn.classList.remove('active');
            }
        });
    }
    
    if (rulerBtn) {
        rulerBtn.addEventListener('click', () => {
            // Toggle ruler mode
            const isActive = chart.rulerMode;
            chart.setRulerMode(!isActive);
            
            // Update button appearance
            if (!isActive) {
                rulerBtn.classList.add('active');
                if (brushBtn) brushBtn.classList.remove('active');
                if (horizontalLineBtn) horizontalLineBtn.classList.remove('active');
                if (rectangleBtn) rectangleBtn.classList.remove('active');
            } else {
                rulerBtn.classList.remove('active');
            }
        });
    }
    
    if (deleteBtn) {
        deleteBtn.addEventListener('click', () => {
            deleteClickCount++;
            
            // Clear previous timer
            if (deleteClickTimer) {
                clearTimeout(deleteClickTimer);
            }
            
            // If second click within 1 second, execute delete
            if (deleteClickCount === 2) {
                deleteClickCount = 0;
                
                // Clear all drawings
                chart.clearDrawnLines();
                
                // Also deactivate all modes if active
                if (brushBtn && chart.drawingMode) {
                    chart.setDrawingMode(false);
                    brushBtn.classList.remove('active');
                }
                if (horizontalLineBtn && chart.horizontalLineMode) {
                    chart.setHorizontalLineMode(false);
                    horizontalLineBtn.classList.remove('active');
                }
                if (rectangleBtn && chart.rectangleMode) {
                    chart.setRectangleMode(false);
                    rectangleBtn.classList.remove('active');
                }
                if (rulerBtn && chart.rulerMode) {
                    chart.setRulerMode(false);
                    rulerBtn.classList.remove('active');
                }
                if (alertBtn && chart.alertMode) {
                    chart.setAlertMode(false);
                    alertBtn.classList.remove('active');
                }
                
                // Visual feedback - briefly highlight button
                deleteBtn.style.backgroundColor = '#4caf50';
                setTimeout(() => {
                    deleteBtn.style.backgroundColor = '';
                }, 200);
            } else {
                // First click - set timer to reset counter
                deleteClickTimer = setTimeout(() => {
                    deleteClickCount = 0;
                }, 1000); // Reset after 1 second
                
                // Visual feedback for first click
                deleteBtn.style.backgroundColor = '#ff9800';
                setTimeout(() => {
                    if (deleteClickCount === 1) {
                        deleteBtn.style.backgroundColor = '';
                    }
                }, 300);
            }
        });
    }
}

if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', initChart);
} else {
    // Use requestAnimationFrame to ensure layout is complete
    requestAnimationFrame(() => {
        setTimeout(initChart, 10);
    });
}

