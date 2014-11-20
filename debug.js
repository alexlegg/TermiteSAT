$(function () {
    $("button.shrink").on("click", function (e) {
        trace = $(this).parent().parent();
        $(trace).find("div.verification").toggle();
        $(trace).find("div.refinement").toggle();
        $(trace).find("div.candidate").toggle();
        if ($(this).html() == "-") {
            $(this).html("+");
        } else {
            $(this).html("-");
        }
    });
});
