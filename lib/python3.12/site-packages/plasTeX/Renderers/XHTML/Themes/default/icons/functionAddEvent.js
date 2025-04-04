function addEvent(elm, evType, fn, useCapture) {
	if (elm.addEventListener) { 
	elm.addEventListener(evType, fn, useCapture); 
	return true; 
	}
	else if (elm.attachEvent) { 
	var r = elm.attachEvent('on' + evType, fn); 
	EventCache.add(elm, evType, fn);
	return r; 
	}
	else {
	elm['on' + evType] = fn;
	}
}
function getEventSrc(e) {
	if (!e) e = window.event;

	if (e.originalTarget)
	return e.originalTarget;
	else if (e.srcElement)
	return e.srcElement;
}
function addLoadEvent(func) {
var oldonload = window.onload;
	if (typeof window.onload != 'function') {
	window.onload = func;
	} else {
	window.onload = 
		function() {
		oldonload();
		func();
		}
	}
}
var EventCache = function(){
	var listEvents = [];
	return {
		listEvents : listEvents,
	
		add : function(node, sEventName, fHandler, bCapture){
			listEvents.push(arguments);
		},
	
		flush : function(){
			var i, item;
			for(i = listEvents.length - 1; i >= 0; i = i - 1){
				item = listEvents[i];
				
				if(item[0].removeEventListener){
					item[0].removeEventListener(item[1], item[2], item[3]);
				};
				
				/* From this point on we need the event names to be prefixed with 'on" */
				if(item[1].substring(0, 2) != "on"){
					item[1] = "on" + item[1];
				};
				
				if(item[0].detachEvent){
					item[0].detachEvent(item[1], item[2]);
				};
				
				item[0][item[1]] = null;
			};
		}
	};
}();


addEvent(window,'unload',EventCache.flush, false);